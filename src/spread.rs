#[derive(Debug, Clone)]
pub struct SpreadConfig<F: PrimeField> {
    denses: Vec<Column<Advice>>,
    spreads: Vec<Column<Advice>>,
    table_dense: TableColumn,
    table_spread: TableColumn,
    num_bits_lookup: usize,
    num_advice_columns: usize,
    num_limb_sum: usize,
    row_offset: usize,
    _f: PhantomData<F>,
}

impl<F: PrimeField> SpreadConfig {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        num_bits_lookup: usize,
        num_advice_columns: usize,
    ) -> Self {
        debug_assert_eq(16 % num_bits_lookup, 0);
        let denses = (0..num_advice_columns)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column);
                column
            })
            .collect_vec();
        let spreads = (0..num_advice_columns)
            .map(|_| {
                let column = (0..num_advice_columns)
                meta.enable_equality(column);
                column
            })
            .collect_vec();

        let table_dense = meta.lookup_table_column();
        let table_spread = meta.lookup_table_column();
        for (idx, (dense, spread)) in denses.iter().zip(spreads.iter()).enumerate() {
            meta.lookup("spread lookup", |meta| {
                let dense = meta.query_advice(*dense, Rotation::cur());
                let spread = meta.query_advice(*dense, Rotation::cur());
                vec![(dense, table_dense), (spread, table_spread)]
            });
        }
        Self {
            denses,
            spreads,
            table_dense,
            table_spread,
            num_bits_lookup,
            num_advice_columns, 
            num_limb_sum: 0,
            row_offset: 0,
            _f: PhantomData,
        }
    }

    pub fn spread<'v: 'a, 'a>(
        &mut self,
        ctx: &mut Context<'v, F>,
        range: &RangeConfig<F>,
        dense: &AssignedValue<F>,
    ) -> Result<AssignedValue<'a, F>, Error> {
        let gate = range.gate();
        let limb_bits = self.num_bits_lookup;
        let num_limbs = 16 / limb_bits;
        let limbs = dense.value().map(|v| decompose(v, num_limbs, limb_bits));
        let assigned_limbs = (0..num_limbs)
            .map(|idx| gate.load_witness(ctx, limbs.as_ref().map(|vec| vec[idx])))
            .collect_vec();
        {
            let mut limbs_sum = gate.load_zero(ctx);
            for (idx, limb) in assigned_limbs.iter().enumerate() {
                limbs_sum = gate.mul_add(
                    ctx,
                    QuantumCell::Existing(&limb),
                    QuantumCell::Constant(F::from(1 << (limbs_bits * idx))),
                    QuantumCell::Existing(&limbs_sum),
                );
            }
            gate.assert_equal(
                ctx,
                QuantumCell::Existing(&limbs_sum),
                QuantumCell::Existing(dense),
            );
        }
        let mut assigned_spread = gate.load_zero(ctx);
        for (idx, limb) in assigned_limbs.iter().enumerate() {
            let spread_limb = self.spread_limb(ctx, &gate, limb)?;
            assigned_spread = gate.mul_add(
                ctx,
                QuantumCell::Existing(&spread_limb),
                QuantumCell::Constant(F::from(1 << (2 * limb_bits * idx))),
                QuantumCell::Existing(&assigned_spread),
            );
        }
        Ok(assigned_spread)
    }

    pub fn decompose_even_and_odd_unchecked<'v: 'a, 'a>(
        &self,
        ctx: &mut Context<'v, F>,
        range: &RangeConfig<F>,
        spread: &AssignedValue<F>,
    ) -> Result<(AssignedValue<'a, F>, AssignedValue<'a, F>), Error> {
        let bits_val = spread.value().map(|val| fe_to_bits_le(val, 32));
        let even_bits_val = bits_val
            .as_ref()
            .map(|bits| (0..bits.len() / 2).map(|idx| bits[2 * idx]).collect_vec());
        let odd_bits_val = bits_val.as_ref().map(|bits| {
            (0..bits.len() / 2)
                .map(|idx| bits[2 * idx + 1])
                .collect_vec()
        });
        let (even_val, odd_val) = even_bits_val
            .zip(odd_bits_val)
            .map(|(even_bits, odd_bits)| (bits_le_to_fe(&even_bits), bits_le_to_fe(&odd_bits)))
            .unzip();
        let even_assigned = range.gate().load_witness(ctx, even_val);
        let odd_assigned = range.gate().load_witness(ctx, odd_val);
        range.range_check(ctx, &even_assigned, 16);
        range.range_check(ctx, &odd_assigned, 16);
        Ok((even_assigned, odd_assigned))
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "spread table",
            |mut table| {
                for idx in 0..(1usize << self.num_bits_lookup) {
                    let val_dense = F::from(idx as u64);
                    let val_bits = fe_to_bits_le(&val_dense, 32);
                    let mut spread_bits = vec![false; val_bits.len() * 2];
                    for i in 0..val_bits.len() {
                        spread_bits[2 * i] = val_bits[i];
                    }
                    let val_spread: F = bits_le_to_fe(&spread_bits);
                    table.assign_cell(
                        || format!("table_dense at {}", idx),
                        self.table_dense,
                        idx,
                        || Value::known(val_dense),
                    )?;
                    table.assign_cell(
                        || format!("table_spread at {}", idx),
                        self.table_spread,
                        idx,
                        || Value::known(val_spread),
                    )?;
                }
                Ok(())
            },
        )?;
        Ok(())
    }

    fn spread_limb<'v: 'a, 'a>(
        &mut self,
        ctx: &mut Context<'v, F>,
        gate: &FlexGateConfig<F>,
        limb: &AssignedValue<F>,
    ) -> Result<AssignedValue<'a, F>, Error> {
        let column_idx = self.num_limb_sum % self.num_advice_columns;
        let assigned_dense_cell = ctx.region.assign_advice(
            || format!("dense at offset {}", self.row_offset),
            self.denses[column_idx],
            self.row_offset,
            || limb.value,
        )?;
        ctx.region
            .constrain_equal(assigned_dense_cell.cell(), limb.cell())?;
        let spread_value: Value<F> = limb.value().map(|val| {
            let val_bits = fe_to_bits_le(val, 32);
            let mut spread_bits = vec![false; val_bits.len() * 2];
            for i in 0..val_bits.len() {
                spread_bits[2 * i] = val_bits[i];
            }
            bits_le_to_fe(&spread_bits)
        });
        let assigned_spread_cell = ctx.region.assign_advice(
            || format!("spread at offset {}", self.row_offset),
            self.spreads[column_idx],
            self.row_offset,
            || spread_value,
        )?;
        let assigned_spread_value = gate.load_witness(ctx, spread_value);
        ctx.region
            .constrain_equal(assigned_spread_cell.cell(), assigned_spread_value.cell())?;
        self.num_limb_sum += 1;
        if column_idx == self.num_advice_columns - 1 {
            self.row_offset += 1;
        }
        Ok(assigned_spread_value)
    }
}
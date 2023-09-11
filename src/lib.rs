use std::task::Context;

use generic_array::GenericArray;
use halo2_base::{gates::range::RangeConfig, halo2_proofs::{halo2curves::group::ff::PrimeField, plonk::{ConstraintSystem, Error}}, QuantumCell, AssignedValue};
use itertools::Itertools;

#[derive(Debug, Clone)]
pub struct AssignedHashResult<'a, F: PrimeField> {
    pub input_len: AssignedValue<'a, F>,
    pub input_bytes: Vec<AssignedValue<'a, F>>,
    pub output_bytes: Vec<AssignedValue<'a, F>>,
}

#[derive(Debug, Clone)]
pub struct Sha256DynamicConfig<F: PrimeField> {
    pub max_variable_byte_sizes: Vec<usize>,
    range: RangeConfig<F>,
    spread_config: SpreadConfig<F>,
    pub cur_hash_idx: usize,
    is_input_range_check: bool,
}

impl<F: PrimeField> Sha256DynamicConfig<F> {
    const ONE_ROUND_INPUT_BYTES: usize = 64;

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        max_variable_byte_sizes: Vec<usize>,
        range: RangeConfig<F>,
        num_bits_lookup: usize,
        num_advice_columns: usize,
        is_input_range_check: bool,
    ) -> Self {
        for byte in max_variable_byte_sizes.iter() {
            debug_assert_eq!(byte % Self::ONE_ROUND_INPUT_BYTES, 0);
        }

        let spread_config = SpreadConfig::configure(meta, num_bits_lookup, num_advice_columns);
        Self {
            max_variable_byte_sizes,
            range,
            spread_config,
            cur_hash_idx: 0,
            is_input_range_check,
        }
    }

    pub fn digest<'a, 'b: 'a>(
        &'a mut self,
        ctx: &mut Context<'b, F>,
        input: &'a [u8],
        precomputed_input_len: Option<usize>,
    ) -> Result<AssignedHashResult<'b, F>, Error> {
        // get input length
        let input_byte_size = input.len();
        // idk why he plus 9, but he added 9 to input_byte_size
        // Last 64 bits = 8 bytes are for input length, first 8 bits = 1 byte after input is 10000000.
        // These 9 bits are needed in SHA256 algorithm.
        let input_byte_size_with_9 = input_byte_size + 9;
        // Just get one_round_input_bytes. It is 64 bytes.
        let one_round_size = Self::ONE_ROUND_INPUT_BYTES;
        // get num round. How many rounds will it have in this one digest.
        let num_round = if input_byte_size_with_9 % one_round_size == 0 {
            input_byte_size_with_9 / one_round_size
        } else {
            input_byte_size_with_9 / one_round_size + 1
        };
        // get padded size. We need to pad some bits to original data for SHA256 algorithm.
        let padded_size = one_round_size * num_round;
        // What is max_variable_byte_size and cur_hash_idx?
        let max_variable_byte_size = self.max_variable_byte_sizes[self.cur_hash_idx];
        // What is variable round? May it be the one for the flexible round num?
        let max_variable_round = mex_variable_byte_size / oun_round_size;
        // Input length that is caluculated beforehand. If the value is empty, return 0.
        let precomputed_input_len = precomputed_input_len.unwrap_or(0);
        // Precomputed_input_len should divided by one_round_size.
        assert_eq!(precomputed_input_len % one_round_size, 0);
        // padded_size can be bigger than max_variable_byte_size?
        // What is max_variable_byte_size?
        assert!(padded_size - precomputed_input_len <= max_variable_byte_size);
        // Yes, zero should be padded. This is in the SHA256 algorithm.
        let zero_padding_byte_size = padded_size - input_byte_size_with9;
        // How many bytes are remained after add padding
        let remaining_byte_size = max_variable_byte_size + precomputed_input_len - padded_size;
        // How many rounds are estimated before inputs to this circuit.
        let precomputed_round = precomputed_input_len / one_round_size;
        // Should be equal since these numbers below are the same.
        assert_eq!(
            remaining_byte_size,
            one_round_size * (max_variable_round + precomputed_round - num_round)
        );
        // change input data into vector form.
        let mut padded_inputs = input.to_vec();
        // 0x80 = 128 = 10000000
        // Add 1 after inputs bits
        padded_inputs.push(0x80);
        // Then add 0 to inputs bits
        for _ in 0..zero_padding_byte_size {
            padded_inputs.push(0);
        }
        // initialize array [0, 0, 0, 0, 0, 0, 0, 0]
        let mut input_len_bytes = [0; 8];
        // get input bits length in hex value
        // For example, input is "abc", then the length will be 24 and this returns 18 0 0 0 0 0 0 0. 
        let le_size_bytes = (8 * input_byte_size).to_le_bytes();
        // get copy of le_size_bytes. Idk why we need copy.
        input_len_bytes[0..le_size_bytes.len()].copy_from_slice(&le_size_bytes);
        // put length information to the latest of padded_inputs
        // This is defined in SHA256 algorithm.
        for byte in input_len_bytes.iter().rev() {
            padded_inputs.push(*byte);
        }
        assert_eq!(padded_inputs.len(), num_round * one_round_size);
        // Do we still need to add 0 pad? I guess it is enough until the upper calculation.
        for _ in 0..remaining_byte_size {
            padded_inputs.push(0);
        }
        assert_eq!(
            padded_inputs.len(),
            max_variable_byte_size + precomputed_input_len
        );

        // initialize RangeConfig which is probably for range check
        let range = self.range().clone();
        // get FlexGateConfig which is inside the RangeConfig.
        let gate = range.gate();
        // convert input_byte_size as u64 into PrimeField and get Value struct which is defined in halo2_proofs
        // Then, call load_witness to assign this number
        let assigned_input_byte_size = 
            gate.load_witness(ctx, Value::known(F::from(input_byte_size as u64)));
        // doing the same thing to num_round
        let assigned_num_round = gate.load_witness(ctx, Value::known(F::from(num_round as u64)));
        // Assign num_round * one_round_size = padded_size
        let assigned_padded_size = gate.mul(
            ctx,
            QuantumCell::Existing(&assigned_num_round),
            QuantumCell::Constant(F::from(one_round_size as u64)),
        );
        // Assign input_byte_size + 9 = input_with_9
        let assigned_input_with_9_size = gate.add(
            ctx,
            QuantumCell::Existing(&assigned_input_byte_size),
            QuantumCell::Constant(F::from(9u64)),
        );
        // Assign padding_size = padded_size - input_with_9_size
        let padding_size = gate.sub(
            ctx,
            QuantumCell::Existing(&assigned_padded_size),
            QuantumCell::Existing(&assigned_input_with_9_size),
        );
        // Check if padding_size is less than one_round_size
        let padding_is_less_than_round = 
            range.is_less_than_safe(ctx, &padding_size, one_round_size as u64);
        // Check if the result of padding_is_less_than_round == 1;
        gate.assert_is_const(ctx, &padding_is_less_than_round, F::one());
        // load precomputed_round as witness
        let assigned_precomputed_round = 
            gate.load_witness(ctx, Value::known(F::from(precompputed_round as u64)));
        // get max_variable_round which is num_round - precomputed_round
        let assigned_target_round = gate.sub(
            ctx,
            QuantumCell::Existing(&assigned_num_round),
            QuantumCell::Existing(&assigned_precomputed_round),
        );

        // 
        let precomputed_input = &padded_inputs[0..precomputed_input_len];
        // Something defined as last_state
        let mut last_state = INIT_STATE;
        // Divid bytes into one_round_size 
        let precomputed_blocks = precomputed_input
            .chunks(one_round_size)
            .map(|bytes| GenericArray::clone_from_slice(bytes))
            .collect_vec();
        // set digested data into last_state
        // Why do we need to calculate compress256 outside zk circuit
        compress256(&mut last_state, &precomputed_blocks[..]);

        // assign last state as witness
        let mut assigned_last_state_vec = vec![last_state
            .iter()
            .map(|state| gate.load_witness(ctx, Value::known(F::from(*state as u64))))
            .collect_vec()];

        // assign padded_inputs as witness
        let assigned_input_bytes = padded_inputs[precomputed_input_len..]
            .iter()
            .map(|byte| gate.load_witness(ctx, Value::known(F::from(*byte as u64))))
            .collect::<Vec<AssignedValue<F>>>();
        // if you want to check each bytes in assigned input bytes are 8, enable is_input_range_check
        if self.is_input_range_check {
            for assigned_byte in assigned_input_bytes.iter() {
                range.range_check(ctx, assigned_byte, 8);
            }
        }
        // This is just a counter for the later while loop.
        let mut num_processed_input = 0;
        // max_variable_byte_size is N in the paper. max_variable_byte_size is the number of 8 bits in the padded message.
        // really? what is max_variable_byte_size?
        while num_processed_input < max_variable_byte_size {
            // Yes, it seems max_variable_byte_size is N in the paper.
            let assigned_input_word_at_round =
                &assigned_input_bytes[num_processed_input..(num_processed_input + one_round_size)];
            // use compression library and get hash
            let new_assigned_hs_out = sha256_compression(
                ctx,
                &range,
                &mut self.spread_config,
                assigned_input_word_at_round,
                &assigned_last_state_vec.last().unwrap(),
            )?;

            // save at the assigned_last_state_vec
            assigned_last_state_vec.push(new_assigned_hs_out);
            // increment for the next round.
            num_processed_input += one_round_size;
        }

        // What is this data used for?
        let zero = gate.load_zero(ctx);
        // I guess this is the last output for the compression
        let mut output_h_out = vec![zero; 8];
        
        // loop for index and state in assigned_last_state_vec
        for (n_round, assigned_state) in assigned_last_state_vec.into_iter().enumerate() {
            // why do we need to check this is_equal?
            // Can assigned_target_round change?
            let selector = gate.is_equal(
                ctx,
                QuantumCell::Constant(F::from(n_round as u64)),
                QuantumCell::Existing(&assigned_target_round),
            );
            // Ah, so assigned_target_round is for the last round
            // is not equal means just return output_h_out
            // is equal means return assigned_state
            for i in 0..8 {
                output_h_out[i] = gate.select(
                    ctx,
                    QuantumCell::Existing(&assigned_state[i]),
                    QuantumCell::Existing(&output_h_out[i]),
                    QuantumCell::Existing(&selector),
                )
            }
        }
        // 
        let output_digest_bytes = output_h_out
            .into_iter()
            .flat_map(|assigned_word| {
                let be_bytes = assigned_word
                    .value()
                    .map(|v| v.get_lower32().to_be_bytes().to_vec());
                let assigned_bytes = (0..4)
                    .map(|idx| {
                        let assigned = gate
                            .load_witness(ctx, be_bytes.as_ref().map(|vs| F::from(vs[idx] as u64)));
                        range.range_check(ctx, &assigned, 8);
                        assigned
                    })
                    .collect::<Vec<AssignedValue<F>>>();
                let mut sum = gate.load_zero(ctx);
                // I guess this is for masking?
                for (idx, assigned_byte) in assigned_bytes.iter().enumerate() {
                    sum = gate.mul_add(
                        ctx,
                        QuantumCell::Existing(assigned_byte),
                        QuantumCell::Constant(F::from(1u64 << (24 - 8 * idx))),
                        QuantumCell::Existing(&sum),
                    );
                }
                // I do not know what is assigned_word and sum?
                gate.assert_equal(
                    ctx,
                    QuantumCell::Existing(&assigned_word),
                    QuantumCell::Existing(&sum),
                );
                assigned_bytes
            })
            .collect::<Vec<AssignedValue<F>>>();
        let result = AssignedHashResult {
            input_len: assigned_input_byte_size,
            input_bytes: assigned_input_bytes,
            output_bytes: output_digest_bytes,
        };
        self.cur_hash_idx += 1;
        Ok(result)
    }

    pub fn new_context<'a, 'b>(&'b self, region: Region<'a, F>) -> Context<'a, F> {
        Context::new(
            region,
            ContextParams {
                max_rows: self.range.gate.max_rows,
                num_context_idx: 1,
                fixed_columns: self.range.gate.constants.clone(),
            },
        )
    }

    pub fn range(&self) -> &RangeConfig<F> {
        &self.range
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.spread_config.load(layouter)
    }
}
use crate::spread::SpreadConfig;
use crate::utils::{bits_le_to_fe, fe_to_bits_le};
use halo2_base::halo2_proofs::halo2curves::FieldExt;
use halo2_base::halo2_proofs::{
    circuit::{AssignedCell, Cell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector, TableColumn, VirtualCells,
    },
    poly::Rotation,
};
use halo2_base::utils::fe_to_bigint;
use halo2_base::ContextParams;
use halo2_base::QuantumCell;
use halo2_base::{
    gates::{flex_gate::FlexGateConfig, range::RangeConfig, GateInstructions, RangeInstructions},
    utils::{bigint_to_fe, bituint_to_fe, fe_to_bigint, modulus, PrimeField},
    AssignedValue, Context,
};
use hex;
use itertools::Itertools;
use sha2::{Digest, Sha256};

pub type SpreadU32<'a, F> = (AssignedValue<'a, F>, AssignedValue<'a, F>);

pub fn sha256_compression<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    assigned_input_bytes: &[AssignedValue<'a, F>],
    pre_state_words: &[AssignedValue]
) -> Result<Vec<AssignedValue<'a, F>>, Error> {
    debug_assert_eq!(assigned_input_bytes.len(), 64);
    debug_assert_eq!(pre_state_words.len(), 8);
    let gate = range.gate();
}

//! Known answers for the typed Fiat–Shamir layer: the pattern renderings and the seed elements of
//! the uni-STARK, PCS and FRI domain separators over KoalaBear with its quartic extension.
use p3_challenger::fs::{DomainSeparator, FieldUnit};
use p3_challenger::CanObserve;
use p3_field::PrimeField32;
use p3_fri::{FriShape, PcsShape};
use p3_uni_stark::StarkShape;

use crate::stark::Challenge;
type F = p3_koala_bear::KoalaBear;

/// A challenger that records what it observes.
struct Recorder(Vec<F>);

impl CanObserve<F> for Recorder {
    fn observe(&mut self, value: F) {
        self.0.push(value);
    }
}

fn show(name: &str, separator: &DomainSeparator<FieldUnit<F>>) {
    let mut recorder = Recorder(vec![]);
    separator.seed(&mut recorder);
    let elems: Vec<u32> = recorder.0.iter().map(|x| x.as_canonical_u32()).collect();
    println!("{name} pattern\n{:#}", separator.pattern());
    println!("{name} seed {:?}", elems);
}

/// `seeds`: the three domain separators on fixed shapes.
pub fn seeds() {
    let stark = StarkShape {
        log_ext_degree: 3,
        log_degree: 3,
        main_width: 2,
        preprocessed_width: 0,
        num_public_values: 3,
        num_periodic_columns: 0,
        num_quotient_chunks: 1,
        opens_main_next_row: true,
        opens_preprocessed_next_row: false,
        has_randomization: false,
        ood_pow_bits: 2,
    };
    show("stark", &stark.domain_separator::<F, Challenge<F>>());
    let pcs = PcsShape {
        claimed_evaluation_counts: vec![vec![vec![2, 2]], vec![vec![4], vec![4]]],
        batch_pow_bits: 1,
    };
    show("pcs", &pcs.domain_separator::<F, Challenge<F>>());
    let fri = FriShape {
        log_arities: vec![2, 1],
        final_poly_len: 4,
        commit_pow_bits: 1,
        query_pow_bits: 3,
        num_queries: 5,
        index_bits: 7,
        log_blowup: 2,
        max_log_arity: 2,
    };
    show("fri", &fri.domain_separator::<F, Challenge<F>>());
}

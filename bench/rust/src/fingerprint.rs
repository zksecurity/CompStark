//! AIR fingerprints, as `CompStark/Stark/Fingerprint.lean` computes them: every constraint and
//! every lookup of an AIR evaluated at one random point of the quartic extension, hashed with the
//! AIR's shape by Plonky3's Poseidon2 sponge. The constraints and interactions come from upstream's
//! symbolic builder (`InteractionSymbolicBuilder`), evaluated with the shared subexpressions of its
//! `Arc` DAG memoised. `fingerprint AIR LOG_N` prints the report, the same JSON as the Lean side's.
use std::collections::HashMap;
use std::sync::Arc;

use p3_air::symbolic::{
    constraint_degree_from_poly_degree, AirLayout, BaseEntry, BaseLeaf, SymbolicExpr,
    SymbolicExpression,
};
use p3_air::{Air, BaseAir};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32, PrimeField64};
use p3_koala_bear::{default_koalabear_poseidon2_24, KoalaBear};
use p3_lookup::InteractionSymbolicBuilder;
use p3_symmetric::{CryptographicHasher, PaddingFreeSponge};
use p3_util::log2_ceil_usize;

type F = KoalaBear;
type EF = BinomialExtensionField<F, 4>;
type E = SymbolicExpression<F>;

/// SplitMix64 seeded with `"AIR_FP_2"`.
struct SplitMix(u64);

impl SplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    fn ext(&mut self) -> EF {
        let coords: Vec<F> = (0..4).map(|_| F::from_u64(self.next() % F::ORDER_U64)).collect();
        EF::from_basis_coefficients_fn(|i| coords[i])
    }

    fn exts(&mut self, n: usize) -> Vec<EF> {
        (0..n).map(|_| self.ext()).collect()
    }
}

/// The random point.
struct Point {
    cur: Vec<EF>,
    next: Vec<EF>,
    prep_cur: Vec<EF>,
    prep_next: Vec<EF>,
    public: Vec<EF>,
    periodic: Vec<EF>,
    first: EF,
    last: EF,
    transition: EF,
}

/// Evaluate `e` at the point, memoising shared subexpressions by address.
fn eval(e: &E, p: &Point, memo: &mut HashMap<*const E, EF>) -> EF {
    let sub = |a: &Arc<E>, memo: &mut HashMap<*const E, EF>| {
        let k = Arc::as_ptr(a);
        if let Some(v) = memo.get(&k) {
            return *v;
        }
        let v = eval(a, p, memo);
        memo.insert(k, v);
        v
    };
    match e {
        SymbolicExpr::Leaf(l) => match l {
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Main { offset: 0 } => p.cur[v.index],
                BaseEntry::Main { .. } => p.next[v.index],
                BaseEntry::Preprocessed { offset: 0 } => p.prep_cur[v.index],
                BaseEntry::Preprocessed { .. } => p.prep_next[v.index],
                BaseEntry::Public => p.public[v.index],
                BaseEntry::Periodic => p.periodic[v.index],
            },
            BaseLeaf::IsFirstRow => p.first,
            BaseLeaf::IsLastRow => p.last,
            BaseLeaf::IsTransition => p.transition,
            BaseLeaf::Constant(c) => EF::from(*c),
        },
        SymbolicExpr::Add { x, y, .. } => sub(x, memo) + sub(y, memo),
        SymbolicExpr::Sub { x, y, .. } => sub(x, memo) - sub(y, memo),
        SymbolicExpr::Neg { x, .. } => -sub(x, memo),
        SymbolicExpr::Mul { x, y, .. } => sub(x, memo) * sub(y, memo),
    }
}

fn coords(x: EF) -> Vec<F> {
    x.as_basis_coefficients_slice().to_vec()
}

fn nat(x: F) -> String {
    x.as_canonical_u32().to_string()
}

fn json_list(xs: impl IntoIterator<Item = String>) -> String {
    format!("[{}]", xs.into_iter().collect::<Vec<_>>().join(","))
}

fn json_lines(xs: Vec<String>) -> String {
    if xs.is_empty() { "[]".into() } else { format!("[\n{}\n]", xs.join(",\n")) }
}

fn ext_json(x: EF) -> String {
    json_list(coords(x).into_iter().map(nat))
}

/// A lookup at the point: its bus (none for a local one) and its tuples, each with its weight,
/// its elements' values and its multiplicity's value.
struct LookupValues {
    bus: Option<String>,
    tuples: Vec<(u32, Vec<EF>, EF)>,
}

/// Plonky3's `get_log_num_quotient_chunks` on the constraints `cs` for a trace of `n` rows.
fn log_quotient_chunks<A: BaseAir<F>>(air: &A, cs: &[E], n: usize) -> usize {
    let periodic: Vec<usize> = air.periodic_columns().iter().map(Vec::len).collect();
    let degree = if periodic.is_empty() {
        cs.iter().map(|c| c.degree_multiple()).max().unwrap_or(0)
    } else {
        let d = cs.iter().map(|c| c.poly_degree(n, &periodic)).max().unwrap_or(0);
        constraint_degree_from_poly_degree(d, n)
    };
    let degree = degree.max(air.max_constraint_degree().unwrap_or(0));
    log2_ceil_usize(degree.max(2) - 1)
}

/// The fingerprint report of `air` for a trace of `2^log_n` rows.
pub fn report<A>(air: &A, log_n: usize) -> String
where
    A: BaseAir<F> + Air<InteractionSymbolicBuilder<F, EF>>,
{
    let n = 1 << log_n;
    let builder = InteractionSymbolicBuilder::<F, EF>::from_air(air, AirLayout::from_air(air));
    assert!(builder.exclusive_interactions().is_empty(), "exclusive interactions");
    let cs = builder.base_constraints();
    let width = air.width();
    let pw = air.preprocessed_width();
    let npub = air.num_public_values();
    let periodic = air.periodic_columns().into_owned();
    let main_next = !air.main_next_row_columns().is_empty();
    let prep_next = pw > 0 && !air.preprocessed_next_row_columns().is_empty();

    let mut rng = SplitMix(0x4149_525f_4650_5f32);
    let point = Point {
        cur: rng.exts(width),
        next: rng.exts(width),
        prep_cur: rng.exts(pw),
        prep_next: rng.exts(pw),
        public: rng.exts(npub),
        periodic: rng.exts(periodic.len()),
        first: rng.ext(),
        last: rng.ext(),
        transition: rng.ext(),
    };
    let mut memo = HashMap::new();
    let mut ev = |e: &E| eval(e, &point, &mut memo);
    let values: Vec<EF> = cs.iter().map(&mut ev).collect();
    let mut lookups: Vec<LookupValues> = builder.local_interactions().iter()
        .map(|l| LookupValues {
            bus: None,
            tuples: l.tuples.iter().map(|(fields, count)| {
                let (count, weight) = count.clone().into_parts();
                (weight, fields.iter().map(&mut ev).collect(), ev(&count))
            }).collect(),
        })
        .collect();
    lookups.extend(builder.global_interactions().iter().map(|i| LookupValues {
        bus: Some(i.bus_name.clone()),
        tuples: vec![(i.count_weight, i.fields.iter().map(&mut ev).collect(), ev(&i.count))],
    }));

    let header = [2, log_n, width, pw, npub, periodic.len(), main_next as usize,
        prep_next as usize, cs.len(), log_quotient_chunks(air, &cs, n), lookups.len()];
    let sponge = PaddingFreeSponge::<_, 24, 16, 8>::new(default_koalabear_poseidon2_24());
    let prep_digest: Option<[F; 8]> = (pw > 0).then(|| {
        let m = air.preprocessed_trace().expect("preprocessed columns without a trace");
        sponge.hash_iter(m.values)
    });

    let num = |k: usize| F::from_u64(k as u64);
    let mut stream: Vec<F> = header.iter().map(|&k| num(k)).collect();
    stream.extend(values.iter().flat_map(|&v| coords(v)));
    for l in &lookups {
        match &l.bus {
            None => stream.push(F::ZERO),
            Some(b) => {
                stream.extend([F::ONE, num(b.len())]);
                stream.extend(b.bytes().map(|x| num(x as usize)));
            }
        }
        stream.push(num(l.tuples.len()));
        for (w, es, c) in &l.tuples {
            stream.extend([num(es.len()), num(*w as usize)]);
            stream.extend(es.iter().flat_map(|&e| coords(e)));
            stream.extend(coords(*c));
        }
    }
    for c in &periodic {
        stream.push(num(c.len()));
        stream.extend(c.iter().copied());
    }
    stream.extend(prep_digest.iter().flatten().copied());
    let digest: [F; 8] = sponge.hash_iter(stream);

    let lookup_json = |l: &LookupValues| {
        let bus = l.bus.as_ref().map_or("null".to_string(), |b| format!("\"{b}\""));
        let tuples = json_list(l.tuples.iter().map(|(w, es, c)| format!(
            "{{\"weight\":{w},\"fields\":{},\"count\":{}}}",
            json_list(es.iter().map(|&e| ext_json(e))), ext_json(*c))));
        format!("{{\"bus\":{bus},\"tuples\":{tuples}}}")
    };
    format!(
        "{{\"fingerprint\":2,\n\"header\":{},\n\"constraints\":{},\n\"lookups\":{},\n\
         \"periodic\":{},\n\"preprocessed\":{},\n\"digest\":{}}}\n",
        json_list(header.iter().map(|k| k.to_string())),
        json_lines(values.iter().map(|&v| ext_json(v)).collect()),
        json_lines(lookups.iter().map(lookup_json).collect()),
        json_list(periodic.iter().map(|c| json_list(c.iter().map(|&x| nat(x))))),
        prep_digest.map_or("null".to_string(), |d| json_list(d.into_iter().map(nat))),
        json_list(digest.into_iter().map(nat)),
    )
}

/// `fingerprint AIR LOG_N`: the fingerprint report of a test AIR (`stark.rs`, `batch.rs`) or of
/// Plonky3's `KeccakAir` for a trace of `2^LOG_N` rows.
pub fn fingerprint(air: &str, log_n: usize) {
    use crate::batch::BatchAir;
    use crate::stark::*;
    let n = 1 << log_n;
    let out = match air {
        "fibonacci" => report(&FibonacciAir, log_n),
        "cube" => report(&CubeAir, log_n),
        "square" => report(&SquareAir, log_n),
        "wide" => report(&WideAir, log_n),
        "mul-fib" => report(&PrepAir { n, next_row: true }, log_n),
        "mul-fib0" => report(&PrepAir { n, next_row: false }, log_n),
        "periodic" => report(&PeriodicAir::<F>::new(), log_n),
        "periodic-cube" => report(&PeriodicCubeAir::<F>::new(), log_n),
        "keccak" => report(&p3_keccak_air::KeccakAir {}, log_n),
        "wide-bus" => report(&BatchAir::<F>::WideBus, log_n),
        "range-table" => report(&BatchAir::<F>::RangeTable { log_height: log_n }, log_n),
        "range-query" => report(&BatchAir::<F>::RangeQuery, log_n),
        "single-table-local" => report(&BatchAir::<F>::SingleLocal, log_n),
        "mul-lookups" => report(&BatchAir::<F>::MulL { reps: 2, local: true,
            global: vec!["MulFib1".into(), "MulFib2".into()] }, log_n),
        _ => panic!("unknown AIR {air}"),
    };
    print!("{out}");
}

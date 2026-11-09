# Carry-less products in shared folds and PCS

CompPoly `50601b6` supplies the approved inline carry-less primitive and kernel-checked refinements for base-field and cubic products. Its [matched native Rust kernel measurements](https://github.com/mitschabaude-bot/CompPoly/blob/50601b6/docs/bench-bf64-clmul.md) include all arithmetic kernels, differential checks and the compiled-code trust contract. CompStark’s shared folds retain the scalar and compile to inline full or mixed products, eliminating challenge lookup-table preparation. Packed induction and mixed-dot products retain full-width weights and accumulate unreduced carry-less products.

The [gate measurements](clmul-gate.json) compare `56e59c8f` with the CLMUL implementation at `e71093e7`, using three-run single-threaded user-instruction medians. All 110 gate entries pass after ratcheting; complete native sumcheck, PCS, coordinate-map, bit-fold and honest-WHIR checks pass. Clocks are diagnostic because the host is loaded.

| Gate kernel | Software instructions | CLMUL instructions | Ratio |
|---|---:|---:|---:|
| `sumcheck-fold/products` | 81,479,167 | 21,643,556 | 0.266 |
| `sumcheck-fold/prepare` | 1,182,475 | 3,829 | 0.003 |
| `sumcheck-fold/fold` | 36,178,276 | 27,127,569 | 0.750 |
| `sumcheck-fold/packed-fold` | 24,026,307 | 14,197,912 | 0.591 |
| `sumcheck-fold/base-fold` | 32,913,018 | 24,526,228 | 0.745 |
| `sumcheck-fold/packed-base-fold` | 20,360,365 | 12,102,803 | 0.594 |
| `sumcheck-fold/constant-fold` | 23,673,576 | 21,969,697 | 0.928 |
| `sumcheck-fold/packed-constant-fold` | 10,727,290 | 10,464,403 | 0.975 |
| `pcs/basis-project` | 86,713,673 | 71,049,890 | 0.819 |
| `pcs/basis-columns` | 54,516,787 | 48,772,881 | 0.895 |
| `pcs/basis-window-ring` | 24,866,656 | 18,228,452 | 0.733 |
| `pcs/basis-packed-dot` | 2,988,823 | 2,370,293 | 0.793 |
| `pcs/basis-tensor-lift` | 19,089,537 | 7,086,313 | 0.371 |
| `pcs/basis-lift` | 29,994,616 | 15,698,001 | 0.523 |

`prepare_eq_prepareClmul`, `Prepared.mul_code`, `extMulFive_code` and `InductionWide.mul_code` identify the compiled paths with the specification functions. The six-product deferred cubic kernel replaces the five-product interpolation implementation in compiled sumcheck products. Pure Lean definitions and theorems retain their kernel semantics.

## Scalar deferred accumulation and fused survivors

CompPoly `5f494a0` retains ten scalar unreduced accumulators in the packed extension dot. The shared PCS layer prepares retained tensor coefficients, reconstructs live weights on demand and accumulates survivor vectors and the residual message in one traversal. Kernel-checked refinements identify the complete weights, both survivors and both message coefficients with the reference operations. `materializeTensorPairs` takes the physical column stride as a scalar so exponentiation stays outside the product loop.

The [fused gate records](fused-pcs-gate.json) compare `2b79a572` with implementation `88bdbd98` using three-run instruction medians. The ratchet includes 112 entries and adds separate tensor-plan and fused-survivor phases; native sumcheck, coordinate-map, packed-fold and honest-WHIR tests and the PCS axiom audit pass. Production Lean/native-Rust phase comparisons are recorded in LeanVM’s `docs/pcs-fused-performance.md`.

| Gate kernel | Before instructions | Fused instructions | Fused / before |
|---|---:|---:|---:|
| `pcs/whir-round` | 73,292 | 68,732 | 0.938 |
| `pcs/basis-tensor-columns` | 25,673,358 | 21,667,458 | 0.844 |
| `pcs/basis-window-ring` | 18,228,452 | 14,222,800 | 0.780 |
| `pcs/basis-tensor-prepare` | — | 4,600,909 | new measured phase |
| `pcs/basis-fused-survivors` | — | 2,356,591 | new measured phase |

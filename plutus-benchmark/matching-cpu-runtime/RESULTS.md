# CEK wall-time results (2026-08-06)

## Outcome

Sparse capture makes `matchData` competitive with shallow `Match`. A `Data` marker in the static
`TySOP` captures a field and a `Unit` marker skips it; the inferred result `TySOP` contains only
the captured fields. Erasure reifies each branch to a byte mask, and the builtin traverses only
the selected constructor's mask and payload before constructing `VConstr`.

Sparse `matchData` beat traditional deconstruction in all 22 cases, shallow `Match` in 3, and
nested `Match` in 6. It was the overall fastest implementation in 3 cases.

Against the fastest existing implementation per case, sparse `matchData` ranged from `0.782013x`
to `2.313987x`, with a median of `1.178107x`. It won both W=1000 cases and the D=10/W=100 sparse
spine. The remaining loss grows with the number of matched constructors: every node still pays
for generic builtin application and unlifting, an intermediate `VConstr`, and generic `Case`
dispatch. Native `Match` performs that dispatch and capture construction directly in the CEK.

`sparse / fastest` is directed as written; less than one means sparse `matchData` won. These are
host wall times, not portable cost-model coefficients.

| Case | Shallow (us) | Nested (us) | Traditional (us) | Sparse `matchData` (us) | Sparse / fastest |
|---|---:|---:|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 0.357901 | 0.377854 | 0.667046 | 0.472792 | 1.321013 |
| `constr_flat_d1_w16_c4` | 1.031776 | 1.067766 | 1.606495 | 1.128484 | 1.093730 |
| `constr_flat_d1_w1000_c1` | 3.893735 | 7.142544 | 1.917121 | 1.603069 | 0.836186 |
| `constr_flat_d1_w1000_c16` | 6.698639 | 9.939033 | 5.745813 | 4.493298 | 0.782013 |
| `constr_spine_front_d4_w16_c8` | 2.034489 | 2.224007 | 3.835260 | 2.299260 | 1.130141 |
| `constr_spine_middle_d4_w16_c8` | 2.045473 | 2.235749 | 4.025645 | 2.264956 | 1.107302 |
| `constr_spine_last_d4_w16_c8` | 2.059960 | 2.137027 | 3.817799 | 2.554383 | 1.240016 |
| `constr_spine_irregular_d4_w16_c8` | 2.073076 | 2.210344 | 3.935280 | 2.310997 | 1.114767 |
| `constr_spine_irregular_d8_w8_c8` | 2.404038 | 2.371215 | 5.718656 | 2.769863 | 1.168120 |
| `constr_spine_front_d64_w2_c8` | 5.498050 | 4.415301 | 17.525628 | 9.086431 | 2.057941 |
| `constr_spine_zigzag_d100_w2_c10` | 8.022903 | 5.985006 | 28.262511 | 13.849227 | 2.313987 |
| `constr_binary_d3_w16_c8` | 2.445819 | 2.607416 | 4.674805 | 2.661273 | 1.088091 |
| `constr_ternary_d3_w8_c10` | 3.139957 | 3.067398 | 7.350378 | 3.748650 | 1.222095 |
| `constr_quaternary_d3_w8_c17` | 5.151877 | 4.783671 | 11.630594 | 6.077036 | 1.270371 |
| `constr_rootfork2_d6_w12_c8` | 2.563802 | 2.638462 | 5.520768 | 2.855564 | 1.113800 |
| `constr_rootfork3_d5_w10_c9` | 2.814644 | 2.762332 | 6.258073 | 3.124216 | 1.131007 |
| `constr_rootfork4_d4_w8_c8` | 2.278199 | 2.308060 | 4.947085 | 2.712580 | 1.190668 |
| `constr_spine_stress_d10_w100_c20` | 8.296058 | 10.892651 | 11.166538 | 6.747983 | 0.813396 |
| `constr_binary_stress_d8_w8_c32` | 28.182496 | 27.443982 | 116.878475 | 42.717893 | 1.556549 |
| `constr_alt_spine_d16_w8_c8` | 3.067825 | 4.632294 | 8.327314 | 3.850168 | 1.255016 |
| `constr_alt_rootfork3_d5_w10_c9` | 2.844845 | 4.093085 | 6.540113 | 3.379943 | 1.188094 |
| `constr_alt_binary_d8_w8_c32` | 28.255839 | 50.902547 | 114.013661 | 43.268227 | 1.531302 |

Complete means, confidence intervals, and standard deviations are in
[`results/2026-08-06-criterion-wall-time.csv`](results/2026-08-06-criterion-wall-time.csv),
and [`results/2026-08-06-matchdata-sparse-criterion-wall-time.csv`](results/2026-08-06-matchdata-sparse-criterion-wall-time.csv).

## Measurement contract

- The baseline implementations use three distinct historical branch bases:
  - Shallow: `sho/shallowBuiltinMatching` at
    `d118a596556784d599bf6e9a80c9fcffa01d2cf0`.
  - Nested: `sho/builtinMatching` at
    `20d7f06ed4dc5f29439b5b0d4b1ab8a62627f3b3`.
  - Traditional: the pre-Match mainline commit
    `b9d726d7cc957fa154c6ba9f01959952887f1246`.
- Sparse `matchData` uses the revision containing this report.
- Runner logic, arguments, case order, expected values, and arithmetic were identical. `Main.hs`
  differed only in its explicit `_shallow`, `_nested`, `_traditional`, or `_matchdata` matcher
  references and in validation serialization. Serialization was not part of the timed action.
- Every successful matcher captures the same `C` integer values and performs the same
  left-associated `C - 1` inline `addInteger` operations. `addInteger` is not hoisted in any
  implementation. Untouched fields are not Data-discriminator inspected.
- All 66 emitted baseline terms were inspected structurally. Traditional terms
  share repeated `tailList`, `dropList`, `unConstrData`, `equalsInteger`, and `unIData` builtin
  values, leave single uses direct, and substitute selected decoding expressions into the result
  continuation without administrative capture lambdas/applications. The sparse `matchData`
  emitter uses a hidden `(array bytestring)` with one byte mask per constructor, cases the returned
  `VConstr` at the same `Data.Constr` index, and binds only the fields selected by that mask.
- GHC 9.6.7, Criterion 1.6.5.0, Cabal `-O1`, one GHC capability (`-N1`), process pinned to CPU 0.
- Host: AMD Ryzen 9 7950X, Linux 7.0.0-27-generic x86_64.
- Criterion wall-clock time, `-L 2`, 1000 bootstrap resamples, with implementation order rotated
  across the three baseline branches by case. Sparse `matchData` was run in listed order.
  Nested `constr_flat_d1_w16_c4` and shallow
  `constr_spine_last_d4_w16_c8` were rerun with `-L 8` after exceeding 2% coefficient of
  variation. The shallow/nested `constr_rootfork3_d5_w10_c9` pair was also rerun with `-L 8` to
  resolve its prior confidence-interval overlap. The largest coefficient of variation in the
  baseline matrix was 1.630382%. All sparse cases used `-L 2`; their largest was 1.3497%.
- Each OS process selected exactly one case. Argument and matcher generation, full forcing,
  `applyTerm`, and exact-result checking happened before timing. Criterion measured only
  `whnf runCEK appliedTerm`.

Execution budgets were not benchmarked. The existing untimed preflight covers the 66 baseline
implementation/case runs, all of which returned the expected integer and passed the protocol
limits. Full validation data is in
[`results/2026-08-06-preflight-validation.csv`](results/2026-08-06-preflight-validation.csv).
`matchData` has `unimplementedCostingFun`, so its counting-mode budgets are deliberately enormous
and no protocol-limit claim is made. Every `matchData` case still returned its exact expected
integer during the untimed setup immediately before Criterion measurement.

## Evaluator-version control

The primary matrix deliberately measures each baseline on its historical branch's complete CEK
runtime and sparse `matchData` on the prototype branch. Those evaluators are not
binary-identical: the pre-Match evaluator, the two Match evaluators, and the prototype have
different internal paths.

As a control, the same optimized traditional UPLC was run under all three evaluators. Relative to
the pre-Match evaluator, the shallow-branch CEK changed individual means by -1.8955% to +5.9637%
(3.1503% mean absolute change), and the nested-branch CEK by -4.6606% to +4.3821% (1.6381% mean
absolute change). Directly comparing the two Match evaluators, the nested-branch CEK ranged from
6.4364% faster to 1.9048% slower than the shallow-branch CEK (3.6825% mean absolute change), and
was faster in 21 of 22 control cases. Every control sample had coefficient of variation below 2%.
Substituting any of the three control means for traditional matching leaves the lowest-mean
implementation unchanged in all 22 cases. The complete control is in
[`results/2026-08-06-traditional-evaluator-sensitivity.csv`](results/2026-08-06-traditional-evaluator-sensitivity.csv).
Sparse `matchData` ranges from 21.7987% faster to 131.3987% slower than the fastest historical
baseline. Small differences, such as its 1.3064% loss on the D=4/W=16 middle spine, are within the
evaluator variation measured by this control; the wide-case wins and deep-tree losses are not.

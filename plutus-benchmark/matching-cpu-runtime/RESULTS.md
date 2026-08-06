# CEK wall-time results (2026-08-06)

## Outcome

Shallow matching had the lowest mean in 13 of 22 cases, nested matching in 7, and traditional
deconstruction in 2. The optimized array-backed `matchData` won none. Its mean was `1.345968x`
to `11.807296x` the fastest existing implementation, with a median ratio of `1.880341x`.

Replacing `[Integer]` with `(array integer)`, indexing it directly, checking only the selected
arity, and removing runtime `TySOP` construction improved 19 of 22 cases. The array/list mean
ratio ranged from `0.298172x` to `1.038156x`, with a median of `0.933240x`. It was faster than
traditional deconstruction in 18 of 22 cases, but never faster than shallow or nested matching.
The clearest boundaries were:

- The D=100/W=2 spine fell from `42.070296 us` to `16.972738 us` (`2.479x` faster).
- The D=8 binary tree fell from `307.455899 us` to `94.772987 us` (`3.244x` faster); its
  terminal-alternative version fell from `317.782897 us` to `94.753825 us` (`3.354x` faster).
- Tag-zero cases changed little because lookup was already constant-depth. D=1/W=16 took
  `1.388737 us`, `1.345968x` shallow and `0.864452x` traditional.
- D=1/W=1000 with one late capture still took `22.636016 us`, `11.807296x` traditional.

The hidden array is unlifted directly as a strict vector. Runtime work is one tag bounds check,
one direct index, one comparison against the selected constructor's field count, and construction
of `VConstr`; neither `matchData` nor the CEK instance constructs a PLC type. The remaining wide
case cost comes from `Case` feeding all `W` fields to the handler even when the source pattern
captures only a sparse subset.

`array / fastest baseline` is directed as written; greater than one means a baseline was faster.
These are host wall times, not portable cost-model coefficients.

| Case | Shallow (us) | Nested (us) | Traditional (us) | List `matchData` (us) | Array `matchData` (us) | Array / fastest baseline |
|---|---:|---:|---:|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 0.357901 | 0.377854 | 0.667046 | 0.513657 | 0.517601 | 1.446212 |
| `constr_flat_d1_w16_c4` | 1.031776 | 1.067766 | 1.606495 | 1.387602 | 1.388737 | 1.345968 |
| `constr_flat_d1_w1000_c1` | 3.893735 | 7.142544 | 1.917121 | 23.270224 | 22.636016 | 11.807296 |
| `constr_flat_d1_w1000_c16` | 6.698639 | 9.939033 | 5.745813 | 25.285131 | 24.734217 | 4.304738 |
| `constr_spine_front_d4_w16_c8` | 2.034489 | 2.224007 | 3.835260 | 3.550008 | 3.371043 | 1.656948 |
| `constr_spine_middle_d4_w16_c8` | 2.045473 | 2.235749 | 4.025645 | 3.507088 | 3.640903 | 1.779981 |
| `constr_spine_last_d4_w16_c8` | 2.059960 | 2.137027 | 3.817799 | 3.537941 | 3.424507 | 1.662414 |
| `constr_spine_irregular_d4_w16_c8` | 2.073076 | 2.210344 | 3.935280 | 3.695254 | 3.401149 | 1.640629 |
| `constr_spine_irregular_d8_w8_c8` | 2.404038 | 2.371215 | 5.718656 | 4.015385 | 3.739383 | 1.576990 |
| `constr_spine_front_d64_w2_c8` | 5.498050 | 4.415301 | 17.525628 | 20.763720 | 12.244688 | 2.773240 |
| `constr_spine_zigzag_d100_w2_c10` | 8.022903 | 5.985006 | 28.262511 | 42.070296 | 16.972738 | 2.835877 |
| `constr_binary_d3_w16_c8` | 2.445819 | 2.607416 | 4.674805 | 5.105599 | 4.884401 | 1.997041 |
| `constr_ternary_d3_w8_c10` | 3.139957 | 3.067398 | 7.350378 | 6.193607 | 5.694395 | 1.856425 |
| `constr_quaternary_d3_w8_c17` | 5.151877 | 4.783671 | 11.630594 | 10.496837 | 9.109339 | 1.904257 |
| `constr_rootfork2_d6_w12_c8` | 2.563802 | 2.638462 | 5.520768 | 5.396487 | 4.999849 | 1.950170 |
| `constr_rootfork3_d5_w10_c9` | 2.814644 | 2.762332 | 6.258073 | 5.471540 | 5.078564 | 1.838506 |
| `constr_rootfork4_d4_w8_c8` | 2.278199 | 2.308060 | 4.947085 | 4.035142 | 3.815984 | 1.675000 |
| `constr_spine_stress_d10_w100_c20` | 8.296058 | 10.892651 | 11.166538 | 28.178468 | 27.073926 | 3.263469 |
| `constr_binary_stress_d8_w8_c32` | 28.182496 | 27.443982 | 116.878475 | 307.455899 | 94.772987 | 3.453325 |
| `constr_alt_spine_d16_w8_c8` | 3.067825 | 4.632294 | 8.327314 | 7.069894 | 6.244932 | 2.035622 |
| `constr_alt_rootfork3_d5_w10_c9` | 2.844845 | 4.093085 | 6.540113 | 5.625446 | 5.261009 | 1.849313 |
| `constr_alt_binary_d8_w8_c32` | 28.255839 | 50.902547 | 114.013661 | 317.782897 | 94.753825 | 3.353425 |

Complete means, confidence intervals, and standard deviations are in
[`results/2026-08-06-criterion-wall-time.csv`](results/2026-08-06-criterion-wall-time.csv) and
[`results/2026-08-06-matchdata-array-criterion-wall-time.csv`](results/2026-08-06-matchdata-array-criterion-wall-time.csv).

## Measurement contract

- The baseline implementations use three distinct historical branch bases:
  - Shallow: `sho/shallowBuiltinMatching` at
    `d118a596556784d599bf6e9a80c9fcffa01d2cf0`.
  - Nested: `sho/builtinMatching` at
    `20d7f06ed4dc5f29439b5b0d4b1ab8a62627f3b3`.
  - Traditional: the pre-Match mainline commit
    `b9d726d7cc957fa154c6ba9f01959952887f1246`.
- List-backed `matchData` uses the `origin/master`-based type-directed builtin prototype at
  `21c747279`; array-backed `matchData` uses the optimized revision containing this report.
- Runner logic, arguments, case order, expected values, and arithmetic were identical. `Main.hs`
  differed only in its explicit `_shallow`, `_nested`, `_traditional`, or `_matchdata` matcher
  references and in validation serialization. Serialization was not part of the timed action.
- Every successful matcher captures the same `C` integer values and performs the same
  left-associated `C - 1` inline `addInteger` operations. `addInteger` is not hoisted in any
  implementation. Untouched fields are not Data-discriminator inspected.
- All 66 emitted baseline terms were inspected structurally. Traditional terms
  share repeated `tailList`, `dropList`, `unConstrData`, `equalsInteger`, and `unIData` builtin
  values, leave single uses direct, and substitute selected decoding expressions into the result
  continuation without administrative capture lambdas/applications. The direct `matchData`
  emitter uses the hidden `(array integer)` arity table `[0, ..., W]` at each constructor node,
  cases the returned `VConstr` at the same `Data.Constr` index, and binds exactly `W` original
  fields before decoding selected integers.
- GHC 9.6.7, Criterion 1.6.5.0, Cabal `-O1`, one GHC capability (`-N1`), process pinned to CPU 0.
- Host: AMD Ryzen 9 7950X, Linux 7.0.0-27-generic x86_64.
- Criterion wall-clock time, `-L 2`, 1000 bootstrap resamples, with implementation order rotated
  across the three baseline branches by case. The `matchData` cases were run in listed order.
  Nested `constr_flat_d1_w16_c4` and shallow
  `constr_spine_last_d4_w16_c8` were rerun with `-L 8` after exceeding 2% coefficient of
  variation. The shallow/nested `constr_rootfork3_d5_w10_c9` pair was also rerun with `-L 8` to
  resolve its prior confidence-interval overlap. List-backed `matchData`
  `constr_flat_d1_w16_c4` and `constr_spine_middle_d4_w16_c8` were rerun at `-L 8` after exceeding
  2%. Array-backed `constr_spine_middle_d4_w16_c8` was likewise rerun at `-L 8`; its largest final
  coefficient of variation was 1.377947%. The largest value in the baseline matrix was
  1.630382%.
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
runtime and both `matchData` revisions on the prototype branch. Those evaluators are not
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
The closest array-backed `matchData` result is still 34.5968% slower than the fastest baseline, well outside
the evaluator variation observed by this control.

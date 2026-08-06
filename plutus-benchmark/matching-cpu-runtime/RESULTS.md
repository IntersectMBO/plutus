# CEK wall-time results (2026-08-06)

## Outcome

Shallow matching had the lowest mean in 13 of 22 cases, nested matching in 7, and traditional
deconstruction in 2. `matchData` won none. Its mean was `1.344868x` to `12.138109x` the fastest
existing implementation in each case, with a median ratio of `2.053325x`. None of its 95% mean
confidence intervals overlapped a baseline interval.

`matchData` was faster than traditional deconstruction in 14 of 22 cases, but never faster than
shallow or nested matching. The clearest boundaries were:

- On D=1/W=16, `matchData` took `1.387602 us`: `1.344868x` shallow, but `0.863745x`
  traditional.
- On D=1/W=1000 with one late capture, it took `23.270224 us`: `12.138109x` traditional,
  which was the fastest implementation for that case.
- On the D=8 binary tree it took `307.455899 us`: `11.203035x` nested. The terminal-alternative
  version took `317.782897 us`: `11.246628x` shallow.
- On the D=100/W=2 spine it took `42.070296 us`: `7.029282x` nested.

The current builtin denotation traverses and validates the entire hidden `[Integer]` arity table
and rebuilds the result `TySOP` on every call. Each emitted match has a table of length
`expectedTag + 1`; high preorder constructor tags therefore amplify that work. Returning a
`VConstr` also makes `Case` feed all `W` fields to the handler, even when the source pattern
captures only a sparse subset. The width-1000 and high-tag branching results expose these costs.

`matchData / fastest baseline` is directed as written; greater than one means a baseline was
faster. These are host wall times, not portable cost-model coefficients.

| Case | Shallow (us) | Nested (us) | Traditional (us) | `matchData` (us) | `matchData` / fastest baseline |
|---|---:|---:|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 0.357901 | 0.377854 | 0.667046 | 0.513657 | 1.435194 |
| `constr_flat_d1_w16_c4` | 1.031776 | 1.067766 | 1.606495 | 1.387602 | 1.344868 |
| `constr_flat_d1_w1000_c1` | 3.893735 | 7.142544 | 1.917121 | 23.270224 | 12.138109 |
| `constr_flat_d1_w1000_c16` | 6.698639 | 9.939033 | 5.745813 | 25.285131 | 4.400619 |
| `constr_spine_front_d4_w16_c8` | 2.034489 | 2.224007 | 3.835260 | 3.550008 | 1.744914 |
| `constr_spine_middle_d4_w16_c8` | 2.045473 | 2.235749 | 4.025645 | 3.507088 | 1.714561 |
| `constr_spine_last_d4_w16_c8` | 2.059960 | 2.137027 | 3.817799 | 3.537941 | 1.717480 |
| `constr_spine_irregular_d4_w16_c8` | 2.073076 | 2.210344 | 3.935280 | 3.695254 | 1.782498 |
| `constr_spine_irregular_d8_w8_c8` | 2.404038 | 2.371215 | 5.718656 | 4.015385 | 1.693387 |
| `constr_spine_front_d64_w2_c8` | 5.498050 | 4.415301 | 17.525628 | 20.763720 | 4.702674 |
| `constr_spine_zigzag_d100_w2_c10` | 8.022903 | 5.985006 | 28.262511 | 42.070296 | 7.029282 |
| `constr_binary_d3_w16_c8` | 2.445819 | 2.607416 | 4.674805 | 5.105599 | 2.087480 |
| `constr_ternary_d3_w8_c10` | 3.139957 | 3.067398 | 7.350378 | 6.193607 | 2.019173 |
| `constr_quaternary_d3_w8_c17` | 5.151877 | 4.783671 | 11.630594 | 10.496837 | 2.194306 |
| `constr_rootfork2_d6_w12_c8` | 2.563802 | 2.638462 | 5.520768 | 5.396487 | 2.104876 |
| `constr_rootfork3_d5_w10_c9` | 2.814644 | 2.762332 | 6.258073 | 5.471540 | 1.980768 |
| `constr_rootfork4_d4_w8_c8` | 2.278199 | 2.308060 | 4.947085 | 4.035142 | 1.771198 |
| `constr_spine_stress_d10_w100_c20` | 8.296058 | 10.892651 | 11.166538 | 28.178468 | 3.396609 |
| `constr_binary_stress_d8_w8_c32` | 28.182496 | 27.443982 | 116.878475 | 307.455899 | 11.203035 |
| `constr_alt_spine_d16_w8_c8` | 3.067825 | 4.632294 | 8.327314 | 7.069894 | 2.304530 |
| `constr_alt_rootfork3_d5_w10_c9` | 2.844845 | 4.093085 | 6.540113 | 5.625446 | 1.977417 |
| `constr_alt_binary_d8_w8_c32` | 28.255839 | 50.902547 | 114.013661 | 317.782897 | 11.246628 |

Complete means, confidence intervals, and standard deviations are in
[`results/2026-08-06-criterion-wall-time.csv`](results/2026-08-06-criterion-wall-time.csv).

## Measurement contract

- The baseline implementations use three distinct historical branch bases:
  - Shallow: `sho/shallowBuiltinMatching` at
    `d118a596556784d599bf6e9a80c9fcffa01d2cf0`.
  - Nested: `sho/builtinMatching` at
    `20d7f06ed4dc5f29439b5b0d4b1ab8a62627f3b3`.
  - Traditional: the pre-Match mainline commit
    `b9d726d7cc957fa154c6ba9f01959952887f1246`.
- `matchData` uses the `origin/master`-based type-directed builtin prototype at `21c747279`.
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
  emitter uses the hidden arity table `[0, ..., W]` at each constructor node, cases the returned
  `VConstr` at the same `Data.Constr` index, and binds exactly `W` original fields before decoding
  selected integers.
- GHC 9.6.7, Criterion 1.6.5.0, Cabal `-O1`, one GHC capability (`-N1`), process pinned to CPU 0.
- Host: AMD Ryzen 9 7950X, Linux 7.0.0-27-generic x86_64.
- Criterion wall-clock time, `-L 2`, 1000 bootstrap resamples, with implementation order rotated
  across the three baseline branches by case. The `matchData` cases were run in listed order.
  Nested `constr_flat_d1_w16_c4` and shallow
  `constr_spine_last_d4_w16_c8` were rerun with `-L 8` after exceeding 2% coefficient of
  variation. The shallow/nested `constr_rootfork3_d5_w10_c9` pair was also rerun with `-L 8` to
  resolve its prior confidence-interval overlap. `matchData` `constr_flat_d1_w16_c4` and
  `constr_spine_middle_d4_w16_c8` were rerun at `-L 8` after exceeding 2%; its largest final
  coefficient of variation was 0.9896%. The largest value in the full matrix was 1.630382%, and
  all pairwise 95% mean confidence intervals were disjoint.
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
runtime and `matchData` on its prototype branch. Those evaluators are not binary-identical: the
pre-Match evaluator, the two Match evaluators, and the prototype have different internal paths.

As a control, the same optimized traditional UPLC was run under all three evaluators. Relative to
the pre-Match evaluator, the shallow-branch CEK changed individual means by -1.8955% to +5.9637%
(3.1503% mean absolute change), and the nested-branch CEK by -4.6606% to +4.3821% (1.6381% mean
absolute change). Directly comparing the two Match evaluators, the nested-branch CEK ranged from
6.4364% faster to 1.9048% slower than the shallow-branch CEK (3.6825% mean absolute change), and
was faster in 21 of 22 control cases. Every control sample had coefficient of variation below 2%.
Substituting any of the three control means for traditional matching leaves the lowest-mean
implementation unchanged in all 22 cases. The complete control is in
[`results/2026-08-06-traditional-evaluator-sensitivity.csv`](results/2026-08-06-traditional-evaluator-sensitivity.csv).
The closest `matchData` result is still 34.4868% slower than the fastest baseline, well outside
the evaluator variation observed by this control.

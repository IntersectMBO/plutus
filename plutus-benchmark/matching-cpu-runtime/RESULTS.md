# CEK wall-time results (2026-08-06)

## Outcome

Shallow matching had the lowest mean in 13 of 22 cases, nested matching in 7, and traditional
deconstruction in 2. No pair of implementations had overlapping 95% mean confidence intervals
in any case.

The clearest boundaries were:

- Traditional won both width-1000 cases. For one late capture it took `1.917121 us`, versus
  shallow `3.893735 us` and nested `7.142544 us`. With 16 scattered captures it took
  `5.745813 us`, versus shallow `6.698639 us` and nested `9.939033 us`.
- Nested won the deep, narrow spines. At D=64/W=2 it took `4.415301 us`, versus shallow
  `5.498050 us` and traditional `17.525628 us`; at D=100/W=2 it took `5.985006 us`, versus
  `8.022903 us` and `28.262511 us`.
- The terminal-alternative cases all favored shallow. The spine means were shallow
  `3.067825 us`, nested `4.632294 us`, traditional `8.327314 us`; the root-fork means were
  `2.844845 us`, `4.093085 us`, `6.540113 us`; and the D=8 binary means were `28.255839 us`,
  `50.902547 us`, `114.013661 us`.

For those alternatives, nested matching traverses a complete failing recursive pattern before
retrying the successful one. Shallow matching shares the structural prefix and retries only the
terminal scalar Match. Traditional code also shares the prefix and dispatches on the terminal
Data constructor, but pays its legacy `unConstrData` and sparse list-deconstruction overhead.

Ratios below are directed as written. A value greater than one means the denominator was faster;
for example, `nested / shallow > 1` favors shallow. These are host wall times, not portable
cost-model coefficients.

| Case | Shallow mean (us) | Nested mean (us) | Traditional mean (us) | Nested / shallow | Traditional / shallow | Traditional / nested |
|---|---:|---:|---:|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 0.357901 | 0.377854 | 0.667046 | 1.055748 | 1.863771 | 1.765356 |
| `constr_flat_d1_w16_c4` | 1.031776 | 1.067766 | 1.606495 | 1.034881 | 1.557019 | 1.504539 |
| `constr_flat_d1_w1000_c1` | 3.893735 | 7.142544 | 1.917121 | 1.834368 | 0.492360 | 0.268409 |
| `constr_flat_d1_w1000_c16` | 6.698639 | 9.939033 | 5.745813 | 1.483739 | 0.857758 | 0.578106 |
| `constr_spine_front_d4_w16_c8` | 2.034489 | 2.224007 | 3.835260 | 1.093152 | 1.885121 | 1.724482 |
| `constr_spine_middle_d4_w16_c8` | 2.045473 | 2.235749 | 4.025645 | 1.093023 | 1.968075 | 1.800580 |
| `constr_spine_last_d4_w16_c8` | 2.059960 | 2.137027 | 3.817799 | 1.037412 | 1.853336 | 1.786500 |
| `constr_spine_irregular_d4_w16_c8` | 2.073076 | 2.210344 | 3.935280 | 1.066215 | 1.898281 | 1.780393 |
| `constr_spine_irregular_d8_w8_c8` | 2.404038 | 2.371215 | 5.718656 | 0.986346 | 2.378771 | 2.411699 |
| `constr_spine_front_d64_w2_c8` | 5.498050 | 4.415301 | 17.525628 | 0.803067 | 3.187608 | 3.969294 |
| `constr_spine_zigzag_d100_w2_c10` | 8.022903 | 5.985006 | 28.262511 | 0.745990 | 3.522729 | 4.722219 |
| `constr_binary_d3_w16_c8` | 2.445819 | 2.607416 | 4.674805 | 1.066071 | 1.911346 | 1.792888 |
| `constr_ternary_d3_w8_c10` | 3.139957 | 3.067398 | 7.350378 | 0.976892 | 2.340917 | 2.396291 |
| `constr_quaternary_d3_w8_c17` | 5.151877 | 4.783671 | 11.630594 | 0.928530 | 2.257545 | 2.431311 |
| `constr_rootfork2_d6_w12_c8` | 2.563802 | 2.638462 | 5.520768 | 1.029121 | 2.153352 | 2.092419 |
| `constr_rootfork3_d5_w10_c9` | 2.814644 | 2.762332 | 6.258073 | 0.981414 | 2.223398 | 2.265504 |
| `constr_rootfork4_d4_w8_c8` | 2.278199 | 2.308060 | 4.947085 | 1.013107 | 2.171490 | 2.143396 |
| `constr_spine_stress_d10_w100_c20` | 8.296058 | 10.892651 | 11.166538 | 1.312991 | 1.346005 | 1.025144 |
| `constr_binary_stress_d8_w8_c32` | 28.182496 | 27.443982 | 116.878475 | 0.973795 | 4.147201 | 4.258802 |
| `constr_alt_spine_d16_w8_c8` | 3.067825 | 4.632294 | 8.327314 | 1.509961 | 2.714404 | 1.797665 |
| `constr_alt_rootfork3_d5_w10_c9` | 2.844845 | 4.093085 | 6.540113 | 1.438773 | 2.298935 | 1.597845 |
| `constr_alt_binary_d8_w8_c32` | 28.255839 | 50.902547 | 114.013661 | 1.801488 | 4.035048 | 2.239842 |

Complete means, confidence intervals, and standard deviations are in
[`results/2026-08-06-criterion-wall-time.csv`](results/2026-08-06-criterion-wall-time.csv).

## Measurement contract

- The implementations use three distinct historical branch bases:
  - Shallow: `sho/shallowBuiltinMatching` at
    `d118a596556784d599bf6e9a80c9fcffa01d2cf0`.
  - Nested: `sho/builtinMatching` at
    `20d7f06ed4dc5f29439b5b0d4b1ab8a62627f3b3`.
  - Traditional: the pre-Match mainline commit
    `b9d726d7cc957fa154c6ba9f01959952887f1246`.
- Runner logic, arguments, case order, expected values, and arithmetic were identical. `Main.hs`
  differed only in its explicit `_shallow`, `_nested`, or `_traditional` matcher references and
  in the traditional branch's UPLC 1.1 validation serialization. Shallow and nested validation
  used UPLC 1.2. Serialization was not part of the timed action.
- Every successful matcher captures the same `C` integer values and performs the same
  left-associated `C - 1` inline `addInteger` operations. `addInteger` is not hoisted in any
  implementation. Untouched fields are not Data-discriminator inspected.
- All 22 emitted terms in each implementation were inspected structurally. Traditional terms
  share repeated `tailList`, `dropList`, `unConstrData`, `equalsInteger`, and `unIData` builtin
  values, leave single uses direct, and substitute selected decoding expressions into the result
  continuation without administrative capture lambdas/applications.
- GHC 9.6.7, Criterion 1.6.5.0, Cabal `-O1`, one GHC capability (`-N1`), process pinned to CPU 0.
- Host: AMD Ryzen 9 7950X, Linux 7.0.0-27-generic x86_64.
- Criterion wall-clock time, `-L 2`, 1000 bootstrap resamples, with implementation order rotated
  across the three branches by case. Nested `constr_flat_d1_w16_c4` and shallow
  `constr_spine_last_d4_w16_c8` were rerun with `-L 8` after exceeding 2% coefficient of
  variation. The shallow/nested `constr_rootfork3_d5_w10_c9` pair was also rerun with `-L 8` to
  resolve its prior confidence-interval overlap. The largest final coefficient of variation was
  1.630382%, and all pairwise 95% mean confidence intervals were disjoint.
- Each OS process selected exactly one case. Argument and matcher generation, full forcing,
  `applyTerm`, and exact-result checking happened before timing. Criterion measured only
  `whnf runCEK appliedTerm`.

Execution budgets were not benchmarked. A separate untimed preflight evaluated every case with
counting mode solely to verify correctness and protocol limits. All 66 implementation/case runs
returned the expected integer and passed the 16,384-byte script, 10,000,000,000-CPU, and
14,000,000-memory limits. The maxima were an 8,879-byte script, 193,778,602 CPU, and 736,289
memory, all from traditional `constr_binary_stress_d8_w8_c32`. Full validation data is in
[`results/2026-08-06-preflight-validation.csv`](results/2026-08-06-preflight-validation.csv).

## Evaluator-version control

The primary matrix deliberately measures each implementation on its historical branch's complete
CEK runtime. Those evaluators are not binary-identical: the pre-Match evaluator and the two Match
evaluators have different internal step-accounting paths even when evaluating a term with no
`Match` node.

As a control, the same optimized traditional UPLC was run under all three evaluators. Relative to
the pre-Match evaluator, the shallow-branch CEK changed individual means by -1.8955% to +5.9637%
(3.1503% mean absolute change), and the nested-branch CEK by -4.6606% to +4.3821% (1.6381% mean
absolute change). Directly comparing the two Match evaluators, the nested-branch CEK ranged from
6.4364% faster to 1.9048% slower than the shallow-branch CEK (3.6825% mean absolute change), and
was faster in 21 of 22 control cases. Every control sample had coefficient of variation below 2%.
Substituting any of the three control means for traditional matching leaves the lowest-mean
implementation unchanged in all 22 cases. The complete control is in
[`results/2026-08-06-traditional-evaluator-sensitivity.csv`](results/2026-08-06-traditional-evaluator-sensitivity.csv).

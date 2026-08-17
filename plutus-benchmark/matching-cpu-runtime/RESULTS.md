# CEK wall-time results (2026-08-06)

## Outcome

Sparse capture makes `matchData` competitive with shallow `Match`. A `Data` marker in the static
`TySOP` captures a field and a `Unit` marker skips it; the inferred result `TySOP` contains only
the captured fields. Erasure reifies each branch to a `ByteString` of skip distances, and the
builtin traverses only the selected constructor's gap program and payload before constructing
`VConstr`.

Sparse `matchData` beat traditional deconstruction in all 22 cases, shallow `Match` in 3, and
nested `Match` in 6. It was the overall fastest implementation in 3 cases.

Against the previous one-byte-per-field mask, gap encoding reduced the W=1000/C=1 mean by 2.21%
and W=1000/C=16 by 3.26%. Across all 22 cases its median change was a 0.30% slowdown: the compact
program helps wide sparse constructors, while narrow constructors do not amortize gap decoding.

Against the fastest existing implementation per case, sparse `matchData` ranged from `0.756532x`
to `2.356582x`, with a median of `1.170790x`. It won both W=1000 cases and the D=10/W=100 sparse
spine. The remaining loss grows with the number of matched constructors: every node still pays
for generic builtin application and unlifting, an intermediate `VConstr`, and generic `Case`
dispatch. Native `Match` performs that dispatch and capture construction directly in the CEK.

`sparse / fastest` is directed as written; less than one means sparse `matchData` won. These are
host wall times, not portable cost-model coefficients.

| Case | Shallow (us) | Nested (us) | Traditional (us) | Sparse `matchData` (us) | Sparse / fastest |
|---|---:|---:|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 0.357901 | 0.377854 | 0.667046 | 0.488463 | 1.364799 |
| `constr_flat_d1_w16_c4` | 1.031776 | 1.067766 | 1.606495 | 1.117144 | 1.082739 |
| `constr_flat_d1_w1000_c1` | 3.893735 | 7.142544 | 1.917121 | 1.567596 | 0.817682 |
| `constr_flat_d1_w1000_c16` | 6.698639 | 9.939033 | 5.745813 | 4.346894 | 0.756532 |
| `constr_spine_front_d4_w16_c8` | 2.034489 | 2.224007 | 3.835260 | 2.444018 | 1.201293 |
| `constr_spine_middle_d4_w16_c8` | 2.045473 | 2.235749 | 4.025645 | 2.277458 | 1.113414 |
| `constr_spine_last_d4_w16_c8` | 2.059960 | 2.137027 | 3.817799 | 2.331962 | 1.132042 |
| `constr_spine_irregular_d4_w16_c8` | 2.073076 | 2.210344 | 3.935280 | 2.293265 | 1.106214 |
| `constr_spine_irregular_d8_w8_c8` | 2.404038 | 2.371215 | 5.718656 | 2.775779 | 1.170615 |
| `constr_spine_front_d64_w2_c8` | 5.498050 | 4.415301 | 17.525628 | 9.454734 | 2.141357 |
| `constr_spine_zigzag_d100_w2_c10` | 8.022903 | 5.985006 | 28.262511 | 14.104160 | 2.356582 |
| `constr_binary_d3_w16_c8` | 2.445819 | 2.607416 | 4.674805 | 2.701425 | 1.104507 |
| `constr_ternary_d3_w8_c10` | 3.139957 | 3.067398 | 7.350378 | 3.667596 | 1.195670 |
| `constr_quaternary_d3_w8_c17` | 5.151877 | 4.783671 | 11.630594 | 6.146930 | 1.284982 |
| `constr_rootfork2_d6_w12_c8` | 2.563802 | 2.638462 | 5.520768 | 2.866522 | 1.118075 |
| `constr_rootfork3_d5_w10_c9` | 2.814644 | 2.762332 | 6.258073 | 3.165187 | 1.145839 |
| `constr_rootfork4_d4_w8_c8` | 2.278199 | 2.308060 | 4.947085 | 2.705599 | 1.187604 |
| `constr_spine_stress_d10_w100_c20` | 8.296058 | 10.892651 | 11.166538 | 6.715242 | 0.809450 |
| `constr_binary_stress_d8_w8_c32` | 28.182496 | 27.443982 | 116.878475 | 43.319059 | 1.578454 |
| `constr_alt_spine_d16_w8_c8` | 3.067825 | 4.632294 | 8.327314 | 3.797539 | 1.237861 |
| `constr_alt_rootfork3_d5_w10_c9` | 2.844845 | 4.093085 | 6.540113 | 3.331238 | 1.170973 |
| `constr_alt_binary_d8_w8_c32` | 28.255839 | 50.902547 | 114.013661 | 44.561736 | 1.577081 |

Complete means, confidence intervals, and standard deviations are in
[`results/2026-08-06-criterion-wall-time.csv`](results/2026-08-06-criterion-wall-time.csv),
and [`results/2026-08-06-matchdata-sparse-criterion-wall-time.csv`](results/2026-08-06-matchdata-sparse-criterion-wall-time.csv).

### Sparse-tag rerun (2026-08-17)

The original gap-program run still encoded an array position and `Case` handler for every tag up
to the selected constructor. The sparse-tag implementation instead stores only sorted
`(original tag, gap program)` entries, binary-searches them, and returns the compact entry index.
This removes unused tags but adds pair decoding and tag lookup. Its geometric-mean CEK wall time
was `1.138459x` the gap-only implementation across the same 22 cases. It still beat traditional
matching in all 22 cases, shallow matching in 3, and nested matching in 6; it was fastest in 3.
These are separate-session host timings, so execution budgets below are the portable comparison.

Complete sparse-tag measurements are in
[`results/2026-08-17-matchdata-sparse-tags-criterion-wall-time.csv`](results/2026-08-17-matchdata-sparse-tags-criterion-wall-time.csv).

## Measurement contract

- The baseline implementations use three distinct historical branch bases:
  - Shallow: `sho/shallowBuiltinMatching` at
    `d118a596556784d599bf6e9a80c9fcffa01d2cf0`.
  - Nested: `sho/builtinMatching` at
    `20d7f06ed4dc5f29439b5b0d4b1ab8a62627f3b3`.
  - Traditional: the pre-Match mainline commit
    `b9d726d7cc957fa154c6ba9f01959952887f1246`.
- The gap-only and sparse-tag `matchData` measurements use their respective reported revisions;
  the execution budgets use the sparse-tag revision containing this report.
- Runner logic, arguments, case order, expected values, and arithmetic were identical. `Main.hs`
  differed only in its explicit `_shallow`, `_nested`, `_traditional`, or `_matchdata` matcher
  references and in validation serialization. Serialization was not part of the timed action.
- Every successful matcher captures the same `C` integer values and performs the same
  left-associated `C - 1` inline `addInteger` operations. `addInteger` is not hoisted in any
  implementation. Untouched fields are not Data-discriminator inspected.
- All 66 emitted baseline terms were inspected structurally. Traditional terms
  share repeated `tailList`, `dropList`, `unConstrData`, `equalsInteger`, and `unIData` builtin
  values, leave single uses direct, and substitute selected decoding expressions into the result
  continuation without administrative capture lambdas/applications. The sparse-tag `matchData`
  emitter uses a hidden `(array (pair integer bytestring))` containing only reachable constructor
  tags, cases the returned `VConstr` at its compact local index, and binds only selected fields.
- GHC 9.6.7, Criterion 1.6.5.0, Cabal `-O1`, one GHC capability (`-N1`), process pinned to CPU 0.
- Host: AMD Ryzen 9 7950X, Linux 7.0.0-27-generic x86_64.
- Criterion wall-clock time, `-L 2`, 1000 bootstrap resamples, with implementation order rotated
  across the three baseline branches by case. Sparse `matchData` was run in listed order.
  Nested `constr_flat_d1_w16_c4` and shallow
  `constr_spine_last_d4_w16_c8` were rerun with `-L 8` after exceeding 2% coefficient of
  variation. The shallow/nested `constr_rootfork3_d5_w10_c9` pair was also rerun with `-L 8` to
  resolve its prior confidence-interval overlap. The largest coefficient of variation in the
  baseline matrix was 1.630382%. Sparse cases used `-L 2`, except
  `constr_alt_binary_d8_w8_c32`, which was rerun with `-L 4`; their largest coefficient of
  variation was 0.7394%.
- Each OS process selected exactly one case. Argument and matcher generation, full forcing,
  `applyTerm`, and exact-result checking happened before timing. Criterion measured only
  `whnf runCEK appliedTerm`.

## Execution-budget results (2026-08-17)

`MatchData` uses the canonical builtin-cost benchmark and cost-model generator. Its fitted CPU
model is `237308 + 1040*x`; memory is `1 + x`. The custom first-argument work measure includes
table entries, encoded gap bytes and work, and constructor-tag word size. The second `Data`
argument has no model term: independent payloads up to a 1 MiB bytestring and a 10,000-node spine
did not affect denotation time. Tag sizes from 64 to 65,536 bits were benchmarked separately and
are covered by the first-argument measure.

The ratios below are `MatchData / baseline`; less than one favors `MatchData`. Geometric means and
wins cover all 22 cases.

| Baseline | CPU geometric mean | CPU wins | Memory geometric mean | Memory wins |
|---|---:|---:|---:|---:|
| Traditional | 0.733898 | 19/22 | 0.429197 | 22/22 |
| Shallow | 1.269017 | 3/22 | 0.505240 | 20/22 |
| Nested | 1.083986 | 6/22 | 0.916367 | 12/22 |

On the 20 cases that also fit the old dense-tag `MatchData` script-size limit, sparse tags improve
the CPU geometric mean against traditional matching from `0.832404` to `0.739246`, and memory from
`0.485248` to `0.441636`. The full binary cases now fit as well: the non-alternative D=8 tree is
4,484 bytes, 131,892,496 CPU, and 236,581 memory, versus traditional matching at 8,879 bytes,
193,778,602 CPU, and 736,289 memory. The D=64 spine is 1,094 bytes, 35,885,260 CPU, and 62,310
memory.

All 22 sparse-tag cases returned the expected integer and passed script-size, CPU, and memory
limits. Full current data is in
[`results/2026-08-17-matchdata-sparse-tags-validation.csv`](results/2026-08-17-matchdata-sparse-tags-validation.csv);
the 66 historical baseline rows are in
[`results/2026-08-06-preflight-validation.csv`](results/2026-08-06-preflight-validation.csv).

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
Sparse `matchData` ranges from 24.3468% faster to 135.6582% slower than the fastest historical
baseline. Small differences, such as its 1.8655% loss on the D=4/W=16 middle spine, are within the
evaluator variation measured by this control; the wide-case wins and deep-tree losses are not.

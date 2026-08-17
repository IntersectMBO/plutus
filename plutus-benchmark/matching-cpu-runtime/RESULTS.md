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

`MatchData` uses the canonical builtin-cost benchmark and repository cost-model generator. The
full-duration 89-point rerun for the explicit representation fitted CPU as
`260,843 + 1,072*x`; memory is `1 + x`. Here `x` is the first argument's custom work measure,
covering table entries, encoded gap bytes and work, and constructor-tag word size. The second
`Data` argument has no model term: independent payloads up to a 1 MiB bytestring and a
10,000-node spine did not affect denotation time. Tag sizes from 64 to 65,536 bits were
benchmarked separately and are covered by the first-argument measure.
The 89 raw Criterion rows used for the refit are in
[`benching-matchdata-explicit-representation-2026-08-17.csv`](../../plutus-core/cost-model/data/benching-matchdata-explicit-representation-2026-08-17.csv).

Changing the PLC type to `forall S. BuiltinRep MatchData S -> Data -> S` erases each type
instantiation to one ordinary UPLC `force`. The comparison matcher emits that force at every
`MatchData` call. All 22 cases returned the expected integer and passed the 16 KiB script-size
limit, 10,000,000,000 CPU limit, and 14,000,000 memory limit.

`MatchData` uses less CPU than traditional matching in 19 of 22 cases, shallow matching in 3,
and nested matching in 5. It uses less memory than traditional matching in all 22 cases, shallow
matching in 19, and nested matching in 12. It produces a smaller script than traditional
matching in all 22 cases.

### CPU

| Case | Shallow | Nested | Traditional | MatchData |
|---|---:|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 251,720 | 339,976 | 481,765 | 691,143 |
| `constr_flat_d1_w16_c4` | 1,388,354 | 1,387,462 | 2,005,238 | 1,521,399 |
| `constr_flat_d1_w1000_c1` | 17,544,410 | 13,383,928 | 2,982,974 | 1,768,503 |
| `constr_flat_d1_w1000_c16` | 21,929,330 | 17,589,406 | 9,640,109 | 5,640,951 |
| `constr_spine_front_d4_w16_c8` | 3,618,046 | 3,746,106 | 6,082,994 | 4,314,104 |
| `constr_spine_middle_d4_w16_c8` | 3,618,046 | 3,746,106 | 6,598,823 | 4,314,104 |
| `constr_spine_last_d4_w16_c8` | 3,618,046 | 3,575,250 | 5,854,164 | 4,314,104 |
| `constr_spine_irregular_d4_w16_c8` | 3,618,046 | 3,746,106 | 6,151,999 | 4,314,104 |
| `constr_spine_irregular_d8_w8_c8` | 3,924,046 | 4,410,546 | 10,189,609 | 6,607,012 |
| `constr_spine_front_d64_w2_c8` | 9,315,886 | 14,943,370 | 29,303,115 | 38,776,332 |
| `constr_spine_zigzag_d100_w2_c10` | 13,900,862 | 20,320,430 | 47,413,347 | 60,000,472 |
| `constr_binary_d3_w16_c8` | 4,678,426 | 4,683,342 | 7,979,231 | 6,085,241 |
| `constr_ternary_d3_w8_c10` | 5,583,602 | 6,115,850 | 13,173,734 | 10,026,811 |
| `constr_quaternary_d3_w8_c17` | 9,349,738 | 10,379,768 | 20,190,093 | 15,911,539 |
| `constr_rootfork2_d6_w12_c8` | 4,762,186 | 5,105,942 | 9,408,724 | 7,227,407 |
| `constr_rootfork3_d5_w10_c9` | 4,992,534 | 5,466,452 | 11,034,419 | 8,047,450 |
| `constr_rootfork4_d4_w8_c8` | 3,924,046 | 4,296,642 | 8,336,134 | 6,607,012 |
| `constr_spine_stress_d10_w100_c20` | 23,787,142 | 20,349,186 | 18,625,485 | 11,821,562 |
| `constr_binary_stress_d8_w8_c32` | 64,039,978 | 76,680,422 | 193,778,602 | 143,063,201 |
| `constr_alt_spine_d16_w8_c8` | 5,695,816 | 11,368,843 | 15,748,590 | 11,595,811 |
| `constr_alt_rootfork3_d5_w10_c9` | 5,044,464 | 9,205,495 | 11,152,344 | 8,242,465 |
| `constr_alt_binary_d8_w8_c32` | 64,091,908 | 147,351,747 | 193,009,841 | 143,258,216 |

### Memory

| Case | Shallow | Nested | Traditional | MatchData |
|---|---:|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 1,700 | 1,236 | 2,565 | 1,706 |
| `constr_flat_d1_w16_c4` | 6,806 | 4,440 | 7,579 | 4,283 |
| `constr_flat_d1_w1000_c1` | 101,600 | 61,182 | 4,333 | 2,711 |
| `constr_flat_d1_w1000_c16` | 119,630 | 72,696 | 25,239 | 14,315 |
| `constr_spine_front_d4_w16_c8` | 17,914 | 10,455 | 22,710 | 10,266 |
| `constr_spine_middle_d4_w16_c8` | 17,914 | 10,455 | 23,810 | 10,266 |
| `constr_spine_last_d4_w16_c8` | 17,914 | 10,437 | 21,450 | 10,266 |
| `constr_spine_irregular_d4_w16_c8` | 17,914 | 10,455 | 22,882 | 10,266 |
| `constr_spine_irregular_d8_w8_c8` | 19,914 | 10,525 | 36,054 | 14,158 |
| `constr_spine_front_d64_w2_c8` | 54,314 | 15,387 | 148,914 | 68,710 |
| `constr_spine_zigzag_d100_w2_c10` | 81,918 | 21,651 | 223,478 | 105,318 |
| `constr_binary_d3_w16_c8` | 24,214 | 13,368 | 29,649 | 13,233 |
| `constr_ternary_d3_w8_c10` | 28,818 | 14,526 | 48,791 | 20,571 |
| `constr_quaternary_d3_w8_c17` | 47,632 | 23,894 | 77,245 | 33,177 |
| `constr_rootfork2_d6_w12_c8` | 24,814 | 13,178 | 35,791 | 15,175 |
| `constr_rootfork3_d5_w10_c9` | 25,716 | 13,485 | 40,974 | 16,894 |
| `constr_rootfork4_d4_w8_c8` | 19,914 | 10,513 | 32,006 | 14,158 |
| `constr_spine_stress_d10_w100_c20` | 128,938 | 75,939 | 59,076 | 26,088 |
| `constr_binary_stress_d8_w8_c32` | 369,862 | 151,706 | 736,289 | 262,081 |
| `constr_alt_spine_d16_w8_c8` | 30,614 | 24,401 | 58,082 | 23,538 |
| `constr_alt_rootfork3_d5_w10_c9` | 26,016 | 21,883 | 41,814 | 18,296 |
| `constr_alt_binary_d8_w8_c32` | 370,162 | 286,767 | 735,045 | 263,483 |

### Script bytes

| Case | Shallow | Nested | Traditional | MatchData |
|---|---:|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 15 | 12 | 29 | 26 |
| `constr_flat_d1_w16_c4` | 43 | 37 | 76 | 51 |
| `constr_flat_d1_w1000_c1` | 266 | 638 | 45 | 29 |
| `constr_flat_d1_w1000_c16` | 383 | 712 | 256 | 139 |
| `constr_spine_front_d4_w16_c8` | 99 | 90 | 221 | 129 |
| `constr_spine_middle_d4_w16_c8` | 99 | 90 | 232 | 129 |
| `constr_spine_last_d4_w16_c8` | 99 | 90 | 212 | 129 |
| `constr_spine_irregular_d4_w16_c8` | 99 | 90 | 224 | 129 |
| `constr_spine_irregular_d8_w8_c8` | 116 | 94 | 348 | 197 |
| `constr_spine_front_d64_w2_c8` | 378 | 197 | 1,663 | 1,102 |
| `constr_spine_zigzag_d100_w2_c10` | 569 | 294 | 2,600 | 1,734 |
| `constr_binary_d3_w16_c8` | 124 | 123 | 305 | 177 |
| `constr_ternary_d3_w8_c10` | 164 | 135 | 488 | 290 |
| `constr_quaternary_d3_w8_c17` | 270 | 218 | 808 | 472 |
| `constr_rootfork2_d6_w12_c8` | 132 | 123 | 362 | 212 |
| `constr_rootfork3_d5_w10_c9` | 142 | 124 | 409 | 236 |
| `constr_rootfork4_d4_w8_c8` | 116 | 94 | 320 | 195 |
| `constr_spine_stress_d10_w100_c20` | 453 | 741 | 605 | 315 |
| `constr_binary_stress_d8_w8_c32` | 2,025 | 1,853 | 8,879 | 4,707 |
| `constr_alt_spine_d16_w8_c8` | 197 | 280 | 584 | 341 |
| `constr_alt_rootfork3_d5_w10_c9` | 175 | 240 | 419 | 249 |
| `constr_alt_binary_d8_w8_c32` | 2,167 | 3,697 | 8,861 | 4,723 |

Full current `MatchData` data is in
[`results/2026-08-17-matchdata-explicit-representation-validation.csv`](results/2026-08-17-matchdata-explicit-representation-validation.csv);
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

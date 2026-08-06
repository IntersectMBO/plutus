# CEK wall-time results (2026-08-06)

## Outcome

Shallow matching had the lower mean in 19 of 22 cases; nested matching had the lower mean in 3.
The quaternary D=3 result has overlapping confidence intervals and is a practical tie.

The three late-failing alternatives show the intended shared-prefix effect:

- D=16 spine: shallow `3.056847 us`, nested `4.422259 us`; nested took `1.446673x` as long.
- Three-branch root fork: shallow `2.897009 us`, nested `4.256832 us`; nested took
  `1.469388x` as long.
- Full binary D=8 tree: shallow `27.204802 us`, nested `55.160553 us`; nested took
  `2.027604x` as long.

In those cases, the nested implementation traverses an entire recursive pattern that fails only
at the final leaf and then retries the complete successful pattern. The shallow implementation
traverses the common prefix once and selects between the two tags only at that leaf.

Other useful boundaries:

- Width 1000: nested took `1.942x` as long for one late capture and `1.572x` as long for
  16 scattered captures.
- Depth 64 and 100 at width 2 remain the clear nested wins: nested used `0.882x` and `0.825x`
  the shallow time.
- All four D=4, W=16 child-position variants favored shallow by similar margins
  (`nested/shallow = 1.084..1.098`).
- Depth 10, width 100, 20 captures: nested took `1.403x` as long.
- The ordinary full binary D=8 tree favored shallow by `1.086x`; adding the late failed
  alternative increased that separation to `2.028x`.

`nested / shallow` greater than one means shallow took less time. These are measured host times,
not portable cost-model coefficients.

| Case | Shallow mean (us) | Nested mean (us) | Nested / shallow |
|---|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 0.523428 | 0.571834 | 1.092479 |
| `constr_flat_d1_w16_c4` | 1.149739 | 1.192643 | 1.037316 |
| `constr_flat_d1_w1000_c1` | 4.074692 | 7.914103 | 1.942258 |
| `constr_flat_d1_w1000_c16` | 6.700562 | 10.532900 | 1.571943 |
| `constr_spine_front_d4_w16_c8` | 2.205260 | 2.390238 | 1.083880 |
| `constr_spine_middle_d4_w16_c8` | 2.168140 | 2.379611 | 1.097536 |
| `constr_spine_last_d4_w16_c8` | 2.156807 | 2.346584 | 1.087990 |
| `constr_spine_irregular_d4_w16_c8` | 2.182638 | 2.365523 | 1.083791 |
| `constr_spine_irregular_d8_w8_c8` | 2.372296 | 2.498239 | 1.053089 |
| `constr_spine_front_d64_w2_c8` | 5.541007 | 4.889722 | 0.882461 |
| `constr_spine_zigzag_d100_w2_c10` | 7.945930 | 6.558813 | 0.825431 |
| `constr_binary_d3_w16_c8` | 2.544759 | 2.786437 | 1.094971 |
| `constr_ternary_d3_w8_c10` | 3.163184 | 3.265554 | 1.032363 |
| `constr_quaternary_d3_w8_c17` | 5.088336 | 5.079893 | 0.998341 |
| `constr_rootfork2_d6_w12_c8` | 2.659316 | 2.843917 | 1.069417 |
| `constr_rootfork3_d5_w10_c9` | 2.829792 | 2.959724 | 1.045916 |
| `constr_rootfork4_d4_w8_c8` | 2.370553 | 2.511833 | 1.059598 |
| `constr_spine_stress_d10_w100_c20` | 8.345620 | 11.708172 | 1.402912 |
| `constr_binary_stress_d8_w8_c32` | 27.086972 | 29.413162 | 1.085879 |
| `constr_alt_spine_d16_w8_c8` | 3.056847 | 4.422259 | 1.446673 |
| `constr_alt_rootfork3_d5_w10_c9` | 2.897009 | 4.256832 | 1.469388 |
| `constr_alt_binary_d8_w8_c32` | 27.204802 | 55.160553 | 2.027604 |

The complete mean confidence intervals and standard deviations are in
[`results/2026-08-06-criterion-wall-time.csv`](results/2026-08-06-criterion-wall-time.csv).

## Measurement contract

- Shallow base: `sho/shallowBuiltinMatching` at
  `d118a596556784d599bf6e9a80c9fcffa01d2cf0`.
- Nested base: `sho/builtinMatching` at
  `20d7f06ed4dc5f29439b5b0d4b1ab8a62627f3b3`.
- Shared runner, arguments, case order, expected values, and documentation were byte-identical.
  Only `MatchingCpuRuntime.Matchers` differed.
- Untouched fields were plain pattern wildcards on both sides. Nested `DataI` patterns and
  shallow follow-up `DataI` matches were used only for the same selected capture fields.
- GHC 9.6.7, Criterion 1.6.5.0, Cabal `-O1`, one GHC capability, process pinned to CPU 0.
- Host: AMD Ryzen 9 7950X, Linux 7.0.0-27-generic x86_64.
- Criterion wall-clock `time`, `-L 2`, 1000 bootstrap resamples. Branch order alternated by
  case. Five samples above 2% relative standard deviation were rerun with `-L 4`; the remaining
  noisy sub-microsecond nested sample was rerun with `-L 8`. The final reruns are reported.
- Each OS process selected exactly one case. Argument/matcher construction, full forcing,
  `applyTerm`, and exact-result checking happened before Criterion timing. The measured action was
  only `whnf runCEK appliedTerm`.

Execution budgets were not benchmarked. A separate untimed preflight evaluated each case with
counting mode solely to assert protocol limits. Every output matched its expected integer and all
44 branch/case combinations passed. The largest matcher script was 3,707 bytes, the largest
reported CPU budget was 147,380,957, and the largest reported memory budget was 371,164, all below
the 16,384-byte, 10,000,000,000-CPU, and 14,000,000-memory bounds. Full preflight data is in
[`results/2026-08-06-preflight-validation.csv`](results/2026-08-06-preflight-validation.csv).

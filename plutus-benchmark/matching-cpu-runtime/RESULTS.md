# CEK wall-time results (2026-08-06)

## Outcome

Shallow matching had the lowest mean in 13 of 22 cases, nested matching in 7, and traditional
deconstruction in 2. No pair of implementations had overlapping 95% mean confidence intervals
in any case.

The clearest boundaries were:

- Traditional won both width-1000 cases. For one late capture it took `1.937125 us`, versus
  shallow `3.877375 us` and nested `7.128766 us`. With 16 scattered captures it took
  `6.515511 us`, versus shallow `6.747585 us` and nested `9.823869 us`.
- Nested won the deep, narrow spines. At D=64/W=2 it took `4.472393 us`, versus shallow
  `5.713195 us` and traditional `22.315628 us`; at D=100/W=2 it took `5.985512 us`, versus
  `8.210567 us` and `35.760130 us`.
- The terminal-alternative cases all favored shallow. The spine means were shallow
  `3.096731 us`, nested `4.634274 us`, traditional `9.948259 us`; the root-fork means were
  `2.820575 us`, `4.079777 us`, `7.392462 us`; and the D=8 binary means were `28.230868 us`,
  `49.950457 us`, `133.768908 us`.

For those alternatives, nested matching traverses a complete failing recursive pattern before
retrying the successful one. Shallow matching shares the structural prefix and retries only the
terminal scalar Match. Traditional code also shares the prefix and dispatches on the terminal
Data constructor, but pays its legacy `unConstrData` and sparse list-deconstruction overhead.

Ratios below are directed as written. A value greater than one means the denominator was faster;
for example, `nested / shallow > 1` favors shallow. These are host wall times, not portable
cost-model coefficients.

| Case | Shallow mean (us) | Nested mean (us) | Traditional mean (us) | Nested / shallow | Traditional / shallow | Traditional / nested |
|---|---:|---:|---:|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 0.355058 | 0.377341 | 0.682628 | 1.062758 | 1.922579 | 1.809047 |
| `constr_flat_d1_w16_c4` | 1.051381 | 1.065579 | 1.751141 | 1.013505 | 1.665563 | 1.643369 |
| `constr_flat_d1_w1000_c1` | 3.877375 | 7.128766 | 1.937125 | 1.838555 | 0.499597 | 0.271734 |
| `constr_flat_d1_w1000_c16` | 6.747585 | 9.823869 | 6.515511 | 1.455909 | 0.965606 | 0.663233 |
| `constr_spine_front_d4_w16_c8` | 2.063844 | 2.209957 | 4.360784 | 1.070796 | 2.112942 | 1.973244 |
| `constr_spine_middle_d4_w16_c8` | 2.077263 | 2.256517 | 4.918947 | 1.086294 | 2.367995 | 2.179885 |
| `constr_spine_last_d4_w16_c8` | 2.101183 | 2.112373 | 4.309560 | 1.005326 | 2.051016 | 2.040151 |
| `constr_spine_irregular_d4_w16_c8` | 2.076929 | 2.205083 | 4.449395 | 1.061704 | 2.142296 | 2.017790 |
| `constr_spine_irregular_d8_w8_c8` | 2.325655 | 2.311724 | 6.520821 | 0.994010 | 2.803865 | 2.820762 |
| `constr_spine_front_d64_w2_c8` | 5.713195 | 4.472393 | 22.315628 | 0.782818 | 3.905981 | 4.989639 |
| `constr_spine_zigzag_d100_w2_c10` | 8.210567 | 5.985512 | 35.760130 | 0.729001 | 4.355379 | 5.974448 |
| `constr_binary_d3_w16_c8` | 2.476651 | 2.579543 | 5.460751 | 1.041545 | 2.204893 | 2.116945 |
| `constr_ternary_d3_w8_c10` | 3.222523 | 3.020371 | 8.830918 | 0.937269 | 2.740374 | 2.923786 |
| `constr_quaternary_d3_w8_c17` | 5.147473 | 4.790342 | 13.957213 | 0.930620 | 2.711469 | 2.913615 |
| `constr_rootfork2_d6_w12_c8` | 2.614682 | 2.665931 | 6.509875 | 1.019600 | 2.489739 | 2.441877 |
| `constr_rootfork3_d5_w10_c9` | 2.811430 | 2.763827 | 7.568592 | 0.983068 | 2.692079 | 2.738446 |
| `constr_rootfork4_d4_w8_c8` | 2.298395 | 2.341264 | 6.119720 | 1.018652 | 2.662606 | 2.613854 |
| `constr_spine_stress_d10_w100_c20` | 8.397115 | 10.847805 | 12.899717 | 1.291849 | 1.536208 | 1.189155 |
| `constr_binary_stress_d8_w8_c32` | 28.045835 | 27.291729 | 139.974304 | 0.973112 | 4.990912 | 5.128818 |
| `constr_alt_spine_d16_w8_c8` | 3.096731 | 4.634274 | 9.948259 | 1.496505 | 3.212504 | 2.146670 |
| `constr_alt_rootfork3_d5_w10_c9` | 2.820575 | 4.079777 | 7.392462 | 1.446434 | 2.620906 | 1.811977 |
| `constr_alt_binary_d8_w8_c32` | 28.230868 | 49.950457 | 133.768908 | 1.769356 | 4.738392 | 2.678032 |

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
  left-associated `C - 1` `addInteger` operations. Untouched fields are not Data-discriminator
  inspected.
- GHC 9.6.7, Criterion 1.6.5.0, Cabal `-O1`, one GHC capability (`-N1`), process pinned to CPU 0.
- Host: AMD Ryzen 9 7950X, Linux 7.0.0-27-generic x86_64.
- Criterion wall-clock time, `-L 2`, 1000 bootstrap resamples, with implementation order rotated
  across the three branches by case. Four samples above 2% coefficient of variation were rerun
  with `-L 4`; every final reported sample was at or below 2%.
- Each OS process selected exactly one case. Argument and matcher generation, full forcing,
  `applyTerm`, and exact-result checking happened before timing. Criterion measured only
  `whnf runCEK appliedTerm`.

Execution budgets were not benchmarked. A separate untimed preflight evaluated every case with
counting mode solely to verify correctness and protocol limits. All 66 implementation/case runs
returned the expected integer and passed the 16,384-byte script, 10,000,000,000-CPU, and
14,000,000-memory limits. The maxima were an 8,392-byte script, 195,170,602 CPU, and 744,989
memory, all from traditional `constr_binary_stress_d8_w8_c32`. Full validation data is in
[`results/2026-08-06-preflight-validation.csv`](results/2026-08-06-preflight-validation.csv).

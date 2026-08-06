# CEK wall-time results (2026-08-06)

## Outcome

Shallow matching had the lower mean in 17 of 22 cases; nested matching had the lower mean in 5.
The three-branch D=5 root-fork confidence intervals overlap and make that case a practical tie.

The three alternatives that fail on the literal final DFS capture show the intended shared-prefix
effect:

- D=16 spine: shallow `3.040982 us`, nested `4.619547 us`; nested took `1.519097x` as long.
- Three-branch root fork: shallow `2.828982 us`, nested `4.062601 us`; nested took
  `1.436065x` as long.
- Full binary D=8 tree: shallow `28.458472 us`, nested `49.560949 us`; nested took
  `1.741518x` as long.

In those cases, the first nested recursive pattern traverses the complete structure and rejects at
the final `B @` versus `I @` capture before retrying the complete successful pattern. The
shallow implementation traverses the common structure once and retries only that final scalar
match.

Other useful boundaries:

- Width 1000: nested took `1.842x` as long for one late capture and `1.466x` as long for
  16 scattered captures.
- Depth 64 and 100 at width 2 remain the clear nested wins: nested used `0.789x` and `0.735x`
  the shallow time.
- All four D=4, W=16 child-position variants favored shallow
  (`nested/shallow = 1.036..1.089`).
- At D=3, binary fan-out favored shallow (`1.060x`), while ternary and quaternary fan-out
  favored nested (`0.955x` and `0.938x`).
- Depth 10, width 100, 20 captures: nested took `1.305x` as long.
- The ordinary full binary D=8 tree slightly favored nested (`0.963x`); adding the terminal
  failed alternative changed that ratio to `1.742x`, favoring shallow.

`nested / shallow` greater than one means shallow took less time. These are measured host times,
not portable cost-model coefficients.

| Case | Shallow mean (us) | Nested mean (us) | Nested / shallow |
|---|---:|---:|---:|
| `constr_flat_d1_w1_c1` | 0.355829 | 0.375950 | 1.056545 |
| `constr_flat_d1_w16_c4` | 1.030976 | 1.058160 | 1.026367 |
| `constr_flat_d1_w1000_c1` | 3.869019 | 7.125848 | 1.841771 |
| `constr_flat_d1_w1000_c16` | 6.699935 | 9.824684 | 1.466385 |
| `constr_spine_front_d4_w16_c8` | 2.042160 | 2.223624 | 1.088859 |
| `constr_spine_middle_d4_w16_c8` | 2.079237 | 2.221718 | 1.068526 |
| `constr_spine_last_d4_w16_c8` | 2.078286 | 2.152300 | 1.035613 |
| `constr_spine_irregular_d4_w16_c8` | 2.055630 | 2.189388 | 1.065069 |
| `constr_spine_irregular_d8_w8_c8` | 2.306767 | 2.410385 | 1.044919 |
| `constr_spine_front_d64_w2_c8` | 5.599646 | 4.416109 | 0.788641 |
| `constr_spine_zigzag_d100_w2_c10` | 8.270316 | 6.077831 | 0.734897 |
| `constr_binary_d3_w16_c8` | 2.468717 | 2.617520 | 1.060275 |
| `constr_ternary_d3_w8_c10` | 3.171569 | 3.028133 | 0.954774 |
| `constr_quaternary_d3_w8_c17` | 5.093764 | 4.780426 | 0.938486 |
| `constr_rootfork2_d6_w12_c8` | 2.591906 | 2.646850 | 1.021198 |
| `constr_rootfork3_d5_w10_c9` | 2.788209 | 2.799651 | 1.004104 |
| `constr_rootfork4_d4_w8_c8` | 2.279493 | 2.353028 | 1.032259 |
| `constr_spine_stress_d10_w100_c20` | 8.278307 | 10.803443 | 1.305030 |
| `constr_binary_stress_d8_w8_c32` | 28.334483 | 27.286384 | 0.963010 |
| `constr_alt_spine_d16_w8_c8` | 3.040982 | 4.619547 | 1.519097 |
| `constr_alt_rootfork3_d5_w10_c9` | 2.828982 | 4.062601 | 1.436065 |
| `constr_alt_binary_d8_w8_c32` | 28.458472 | 49.560949 | 1.741518 |

The complete mean confidence intervals and standard deviations are in
[`results/2026-08-06-criterion-wall-time.csv`](results/2026-08-06-criterion-wall-time.csv).

## Measurement contract

- Shallow base: `sho/shallowBuiltinMatching` at
  `d118a596556784d599bf6e9a80c9fcffa01d2cf0`.
- Nested base: `sho/builtinMatching` at
  `20d7f06ed4dc5f29439b5b0d4b1ab8a62627f3b3`.
- Runner logic, arguments, case order, expected values, and documentation were identical.
  `Main.hs` differed only in whether each case referenced its explicit `*_shallow` or
  `*_nested` matcher; the matcher implementations were branch-specific.
- Every successful matcher captures the same `C` integers, uses one handler binder per capture,
  and performs the same left-associated `C - 1` `addInteger` operations. No nested-only handler
  specialization was used.
- Untouched fields were plain pattern wildcards on both sides. Nested `DataI` patterns and
  shallow follow-up `DataI` matches were used only for the same selected capture fields.
- GHC 9.6.7, Criterion 1.6.5.0, Cabal `-O1`, one GHC capability, process pinned to CPU 0.
- Host: AMD Ryzen 9 7950X, Linux 7.0.0-27-generic x86_64.
- Criterion wall-clock `time`, `-L 2`, 1000 bootstrap resamples. Branch order alternated by
  case. The only sample above 2% relative standard deviation was rerun with `-L 4); that final
  rerun is reported.
- Each OS process selected exactly one case. Argument/matcher construction, full forcing,
  `applyTerm`, and exact-result checking happened before Criterion timing. The measured action was
  only `whnf runCEK appliedTerm`.

Execution budgets were not benchmarked. A separate untimed preflight evaluated each case with
counting mode solely to assert protocol limits. Every output matched its expected integer and all
44 branch/case combinations passed. The largest matcher script was 3,697 bytes, the largest
reported CPU budget was 147,351,747, and the largest reported memory budget was 370,162, all below
the 16,384-byte, 10,000,000,000-CPU, and 14,000,000-memory bounds. Full preflight data is in
[`results/2026-08-06-preflight-validation.csv`](results/2026-08-06-preflight-validation.csv).

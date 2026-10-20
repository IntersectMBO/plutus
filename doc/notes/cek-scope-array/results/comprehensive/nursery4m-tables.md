# Comprehensive performance tables

Candidate: `ra-erased-context`; baseline: recorded origin/master `5d9feef021f9`.

8 adjacent paired rounds, 15 workload/mode combinations, 240 measurements.

Negative changes mean less time or allocation. Time changes are equal-workload geometric means; allocation and summed time count one execution of each workload. Intervals bootstrap paired rounds on this fixed corpus. Per-script intervals are nominal, without a multiple-comparison correction.

## By suite

| Suite / mode | N | Time change [95% interval] | CPU time | Sum of times | Allocated bytes | Faster point estimates |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| marlowe-semantics/cek | 1 | -0.00% [-0.87%, +0.82%] | -0.00% | -0.00% | -0.20% | 1/1 |
| nofib/cek | 2 | +2.79% [+0.86%, +5.34%] | +2.79% | +3.54% | -2.88% | 0/2 |
| validation/cek | 6 | -2.74% [-3.93%, -1.00%] | -2.74% | -2.56% | -5.04% | 3/6 |
| validation/full | 6 | +2.79% [+1.65%, +4.23%] | +2.79% | +3.19% | -2.97% | 1/6 |
| all/cek | 9 | -1.23% [-2.28%, +0.21%] | -1.23% | +2.73% | -2.70% | 4/9 |

## Absolute totals and GC

Sum of mean per-evaluation times/bytes across the suite. GC shares include ordinary collections inside evaluation; forced collections between samples are excluded.

| Suite / mode | Master total ms | Candidate total ms | Master total MB | Candidate total MB | Master GC CPU share | Candidate GC CPU share |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| marlowe-semantics/cek | 2.688 | 2.688 | 22.316 | 22.271 | 15.83% | 16.19% |
| nofib/cek | 17.866 | 18.498 | 149.995 | 145.682 | 0.98% | 0.91% |
| validation/cek | 1.336 | 1.302 | 12.307 | 11.686 | 5.08% | 4.88% |
| validation/full | 2.829 | 2.919 | 20.918 | 20.297 | 15.73% | 17.45% |
| all/cek | 21.889 | 22.488 | 184.617 | 179.639 | 3.05% | 2.97% |

## By family

| Family / mode | N | Time change [95% interval] | Allocation |
| --- | ---: | ---: | ---: |
| marlowe-semantics/cek/marlowe-semantics | 1 | -0.00% [-0.87%, +0.82%] | -0.20% |
| nofib/cek/primetest | 2 | +2.79% [+0.86%, +5.34%] | -2.88% |
| validation/cek/coop | 3 | +3.65% [+1.99%, +6.04%] | -3.93% |
| validation/cek/future-increase-margin | 1 | -8.41% [-9.31%, -7.12%] | -6.04% |
| validation/cek/future-settle-early | 1 | -8.30% [-9.20%, -7.06%] | -6.04% |
| validation/cek/vesting | 1 | -9.50% [-10.58%, -8.26%] | -6.34% |
| validation/full/coop | 3 | +1.55% [+0.33%, +3.16%] | -2.72% |
| validation/full/future-increase-margin | 1 | +4.39% [+3.62%, +5.24%] | -3.31% |
| validation/full/future-settle-early | 1 | +9.17% [+3.76%, +19.27%] | -3.31% |
| validation/full/vesting | 1 | -1.16% [-1.74%, -0.62%] | -2.75% |

## Independent repository Criterion benchmarks

Every benchmark runs without `--quick`. These use separate complete processes, so process drift is less controlled than in the adjacent-pair harness.

| Target | Workloads | Change across paired process rounds | Each process-pair change |
| --- | ---: | ---: | --- |
| validation | 89 | -0.20% | -5.20%, +5.07% |
| validation-full | 89 | -4.28% | -2.76%, -5.79% |
| marlowe | 200 | -5.30% | -6.94%, -3.64% |
| nofib | 22 | -4.33% | -2.90%, -5.73% |
| force-delay | 16 | -11.87% | -11.83%, -11.90% |

## Every workload

Absolute time and allocation are arithmetic means across rounds, per evaluation. Time ratio and interval use paired log ratios. `full` means deserialization plus ledger evaluation, with the repository’s V1/semantics A configuration; `cek` validation uses V3/semantics E.

| Workload | Mode | Master µs | Candidate µs | Time change [95% interval] | Master bytes | Candidate bytes | Nominal interval | Native Criterion change |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- | ---: |
| marlowe/semantics/f339f59bdf92495ed2b14e2e4d3705972b4dda59aa929cffe0f1ff5355db8d79 | cek | 2687.71 | 2687.66 | -0.00% [-0.87%, +0.82%] | 22315947 | 22271340 | inconclusive | +2.42% |
| nofib/primetest/05digits | cek | 2446.93 | 2496.14 | +2.00% [+0.86%, +3.55%] | 22000001 | 21305145 | slower | +0.19% |
| nofib/primetest/30digits | cek | 15419.16 | 16002.26 | +3.60% [+0.71%, +8.15%] | 127994939 | 124376910 | slower | -2.63% |
| validation/coop-1 | cek | 118.78 | 122.81 | +3.37% [+1.49%, +5.77%] | 1113687 | 1076655 | slower | +6.75% |
| validation/coop-1 | full | 214.43 | 219.20 | +2.21% [+1.08%, +3.80%] | 1739911 | 1702879 | slower | +3.15% |
| validation/coop-2 | cek | 377.89 | 390.63 | +3.34% [+1.93%, +5.65%] | 3384376 | 3233560 | slower | +9.40% |
| validation/coop-2 | full | 663.96 | 664.68 | +0.10% [-0.79%, +1.30%] | 4749710 | 4598897 | inconclusive | -12.25% |
| validation/coop-7 | cek | 166.19 | 173.30 | +4.25% [+2.53%, +6.69%] | 1552365 | 1502237 | slower | +3.86% |
| validation/coop-7 | full | 289.96 | 296.61 | +2.36% [-0.33%, +5.18%] | 2270115 | 2219987 | inconclusive | +5.46% |
| validation/future-increase-margin-2 | cek | 255.20 | 233.74 | -8.41% [-9.31%, -7.12%] | 2369198 | 2226006 | faster | -2.09% |
| validation/future-increase-margin-2 | full | 587.62 | 613.42 | +4.39% [+3.62%, +5.24%] | 4325328 | 4182142 | slower | +4.54% |
| validation/future-settle-early-2 | cek | 254.14 | 233.07 | -8.30% [-9.20%, -7.06%] | 2369219 | 2226027 | faster | +0.65% |
| validation/future-settle-early-2 | full | 588.14 | 646.20 | +9.17% [+3.76%, +19.27%] | 4325382 | 4182192 | slower | +3.60% |
| validation/vesting-1 | cek | 163.51 | 148.00 | -9.50% [-10.58%, -8.26%] | 1517746 | 1421450 | faster | -5.71% |
| validation/vesting-1 | full | 484.90 | 479.28 | -1.16% [-1.74%, -0.62%] | 3507642 | 3411346 | faster | -3.75% |

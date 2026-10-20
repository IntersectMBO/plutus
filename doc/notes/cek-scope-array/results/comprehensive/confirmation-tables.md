# Comprehensive performance tables

Candidate: `ra-erased-context`; baseline: recorded origin/master `5d9feef021f9`.

12 adjacent paired rounds, 15 workload/mode combinations, 360 measurements.

Negative changes mean less time or allocation. Time changes are equal-workload geometric means; allocation and summed time count one execution of each workload. Intervals bootstrap paired rounds on this fixed corpus. Per-script intervals are nominal, without a multiple-comparison correction.

## By suite

| Suite / mode | N | Time change [95% interval] | CPU time | Sum of times | Allocated bytes | Faster point estimates |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| marlowe-semantics/cek | 1 | +1.40% [+0.75%, +2.01%] | +1.39% | +1.40% | -0.20% | 0/1 |
| nofib/cek | 2 | +1.74% [+1.45%, +2.06%] | +1.75% | +1.51% | -2.88% | 0/2 |
| validation/cek | 6 | -3.51% [-3.64%, -3.39%] | -3.52% | -3.37% | -5.04% | 3/6 |
| validation/full | 6 | +2.30% [+2.16%, +2.45%] | +2.30% | +2.26% | -2.97% | 2/6 |
| all/cek | 9 | -1.83% [-1.89%, -1.77%] | -1.83% | +1.20% | -2.70% | 3/9 |

## Absolute totals and GC

Sum of mean per-evaluation times/bytes across the suite. GC shares include ordinary collections inside evaluation; forced collections between samples are excluded.

| Suite / mode | Master total ms | Candidate total ms | Master total MB | Candidate total MB | Master GC CPU share | Candidate GC CPU share |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| marlowe-semantics/cek | 2.657 | 2.695 | 22.316 | 22.271 | 15.89% | 16.09% |
| nofib/cek | 17.786 | 18.054 | 149.995 | 145.682 | 0.98% | 0.92% |
| validation/cek | 1.332 | 1.287 | 12.307 | 11.686 | 5.10% | 4.94% |
| validation/full | 2.815 | 2.878 | 20.918 | 20.297 | 15.77% | 17.52% |
| all/cek | 21.776 | 22.036 | 184.617 | 179.639 | 3.05% | 3.01% |

## By family

| Family / mode | N | Time change [95% interval] | Allocation |
| --- | ---: | ---: | ---: |
| marlowe-semantics/cek/marlowe-semantics | 1 | +1.40% [+0.75%, +2.01%] | -0.20% |
| nofib/cek/primetest | 2 | +1.74% [+1.45%, +2.06%] | -2.88% |
| validation/cek/coop | 3 | +2.70% [+2.52%, +2.95%] | -3.93% |
| validation/cek/future-increase-margin | 1 | -9.13% [-9.35%, -8.91%] | -6.04% |
| validation/cek/future-settle-early | 1 | -9.09% [-9.40%, -8.78%] | -6.04% |
| validation/cek/vesting | 1 | -9.84% [-10.21%, -9.37%] | -6.34% |
| validation/full/coop | 3 | +1.77% [+1.57%, +1.95%] | -2.72% |
| validation/full/future-increase-margin | 1 | +4.90% [+4.49%, +5.31%] | -3.31% |
| validation/full/future-settle-early | 1 | +4.33% [+3.70%, +4.94%] | -3.31% |
| validation/full/vesting | 1 | -0.62% [-1.15%, +0.00%] | -2.75% |

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
| marlowe/semantics/f339f59bdf92495ed2b14e2e4d3705972b4dda59aa929cffe0f1ff5355db8d79 | cek | 2657.43 | 2694.63 | +1.40% [+0.75%, +2.01%] | 22315948 | 22271341 | slower | +2.42% |
| nofib/primetest/05digits | cek | 2432.71 | 2483.23 | +2.08% [+1.71%, +2.43%] | 22000008 | 21305160 | slower | +0.19% |
| nofib/primetest/30digits | cek | 15353.50 | 15570.96 | +1.41% [+1.01%, +1.90%] | 127994573 | 124376477 | slower | -2.63% |
| validation/coop-1 | cek | 118.30 | 120.87 | +2.17% [+1.78%, +2.59%] | 1113688 | 1076656 | slower | +6.75% |
| validation/coop-1 | full | 213.19 | 218.11 | +2.30% [+1.95%, +2.64%] | 1739911 | 1702879 | slower | +3.15% |
| validation/coop-2 | cek | 375.94 | 384.94 | +2.39% [+2.03%, +2.75%] | 3384368 | 3233552 | slower | +9.40% |
| validation/coop-2 | full | 662.31 | 660.22 | -0.32% [-0.56%, -0.05%] | 4749747 | 4598931 | faster | -12.25% |
| validation/coop-7 | cek | 165.65 | 171.55 | +3.55% [+3.16%, +4.13%] | 1552360 | 1502232 | slower | +3.86% |
| validation/coop-7 | full | 280.97 | 290.42 | +3.36% [+3.18%, +3.55%] | 2270107 | 2219979 | slower | +5.46% |
| validation/future-increase-margin-2 | cek | 254.80 | 231.54 | -9.13% [-9.35%, -8.91%] | 2369199 | 2226007 | faster | -2.09% |
| validation/future-increase-margin-2 | full | 587.32 | 616.07 | +4.90% [+4.49%, +5.31%] | 4325337 | 4182145 | slower | +4.54% |
| validation/future-settle-early-2 | cek | 254.35 | 231.22 | -9.09% [-9.40%, -8.78%] | 2369238 | 2226046 | faster | +0.65% |
| validation/future-settle-early-2 | full | 589.80 | 615.31 | +4.33% [+3.70%, +4.94%] | 4325355 | 4182165 | slower | +3.60% |
| validation/vesting-1 | cek | 162.85 | 146.84 | -9.84% [-10.21%, -9.37%] | 1517745 | 1421449 | faster | -5.71% |
| validation/vesting-1 | full | 481.14 | 478.18 | -0.62% [-1.15%, +0.00%] | 3507640 | 3411343 | inconclusive | -3.75% |

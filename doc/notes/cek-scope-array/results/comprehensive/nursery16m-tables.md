# Comprehensive performance tables

Candidate: `ra-erased-context`; baseline: recorded origin/master `5d9feef021f9`.

8 adjacent paired rounds, 15 workload/mode combinations, 240 measurements.

Negative changes mean less time or allocation. Time changes are equal-workload geometric means; allocation and summed time count one execution of each workload. Intervals bootstrap paired rounds on this fixed corpus. Per-script intervals are nominal, without a multiple-comparison correction.

## By suite

| Suite / mode | N | Time change [95% interval] | CPU time | Sum of times | Allocated bytes | Faster point estimates |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| marlowe-semantics/cek | 1 | +0.97% [-0.05%, +1.95%] | +0.97% | +0.97% | -0.20% | 0/1 |
| nofib/cek | 2 | +0.92% [-1.00%, +2.44%] | +0.92% | +0.50% | -2.86% | 0/2 |
| validation/cek | 6 | -3.49% [-5.89%, -1.09%] | -3.50% | -3.23% | -5.04% | 3/6 |
| validation/full | 6 | -0.31% [-1.63%, +0.49%] | -0.31% | -0.76% | -2.97% | 4/6 |
| all/cek | 9 | -2.04% [-4.02%, -0.24%] | -2.04% | +0.33% | -2.69% | 3/9 |

## Absolute totals and GC

Sum of mean per-evaluation times/bytes across the suite. GC shares include ordinary collections inside evaluation; forced collections between samples are excluded.

| Suite / mode | Master total ms | Candidate total ms | Master total MB | Candidate total MB | Master GC CPU share | Candidate GC CPU share |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| marlowe-semantics/cek | 2.364 | 2.386 | 22.299 | 22.255 | 1.61% | 1.64% |
| nofib/cek | 18.014 | 18.104 | 149.869 | 145.576 | 0.33% | 0.31% |
| validation/cek | 1.304 | 1.262 | 12.298 | 11.677 | 1.38% | 1.35% |
| validation/full | 2.509 | 2.490 | 20.901 | 20.280 | 4.56% | 5.07% |
| all/cek | 21.681 | 21.752 | 184.467 | 179.508 | 0.53% | 0.52% |

## By family

| Family / mode | N | Time change [95% interval] | Allocation |
| --- | ---: | ---: | ---: |
| marlowe-semantics/cek/marlowe-semantics | 1 | +0.97% [-0.05%, +1.95%] | -0.20% |
| nofib/cek/primetest | 2 | +0.92% [-1.00%, +2.44%] | -2.86% |
| validation/cek/coop | 3 | +1.95% [-0.76%, +3.78%] | -3.93% |
| validation/cek/future-increase-margin | 1 | -9.38% [-10.42%, -8.69%] | -6.04% |
| validation/cek/future-settle-early | 1 | -5.97% [-10.27%, +2.08%] | -6.04% |
| validation/cek/vesting | 1 | -10.55% [-11.68%, -9.74%] | -6.34% |
| validation/full/coop | 3 | +0.69% [-1.00%, +1.63%] | -2.72% |
| validation/full/future-increase-margin | 1 | -0.50% [-1.81%, +0.66%] | -3.31% |
| validation/full/future-settle-early | 1 | -2.08% [-3.19%, -1.13%] | -3.31% |
| validation/full/vesting | 1 | -1.33% [-2.22%, -0.58%] | -2.75% |

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
| marlowe/semantics/f339f59bdf92495ed2b14e2e4d3705972b4dda59aa929cffe0f1ff5355db8d79 | cek | 2363.50 | 2386.33 | +0.97% [-0.05%, +1.95%] | 22299391 | 22254813 | inconclusive | +2.42% |
| nofib/primetest/05digits | cek | 2466.37 | 2502.35 | +1.46% [-0.76%, +3.77%] | 21983936 | 21289551 | inconclusive | +0.19% |
| nofib/primetest/30digits | cek | 15547.54 | 15601.95 | +0.37% [-1.28%, +1.43%] | 127885557 | 124286544 | inconclusive | -2.63% |
| validation/coop-1 | cek | 117.99 | 119.38 | +1.23% [-1.44%, +2.81%] | 1112872 | 1075867 | inconclusive | +6.75% |
| validation/coop-1 | full | 204.60 | 206.75 | +1.07% [-0.46%, +2.06%] | 1738198 | 1701213 | inconclusive | +3.15% |
| validation/coop-2 | cek | 368.78 | 373.23 | +1.26% [-1.09%, +2.68%] | 3381936 | 3231250 | inconclusive | +9.40% |
| validation/coop-2 | full | 588.13 | 579.37 | -1.47% [-3.06%, -0.39%] | 4745887 | 4595137 | faster | -12.25% |
| validation/coop-7 | cek | 164.61 | 170.11 | +3.38% [-0.00%, +6.56%] | 1551228 | 1501138 | inconclusive | +3.86% |
| validation/coop-7 | full | 266.22 | 272.83 | +2.51% [+0.40%, +3.76%] | 2267423 | 2217322 | slower | +5.46% |
| validation/future-increase-margin-2 | cek | 246.83 | 223.66 | -9.38% [-10.42%, -8.69%] | 2367464 | 2224377 | faster | -2.09% |
| validation/future-increase-margin-2 | full | 511.13 | 508.55 | -0.50% [-1.81%, +0.66%] | 4322036 | 4178952 | inconclusive | +4.54% |
| validation/future-settle-early-2 | cek | 246.20 | 232.78 | -5.97% [-10.27%, +2.08%] | 2367484 | 2224400 | inconclusive | +0.65% |
| validation/future-settle-early-2 | full | 513.06 | 502.36 | -2.08% [-3.19%, -1.13%] | 4322097 | 4178993 | faster | +3.60% |
| validation/vesting-1 | cek | 159.46 | 142.63 | -10.55% [-11.68%, -9.74%] | 1516632 | 1420407 | faster | -5.71% |
| validation/vesting-1 | full | 426.22 | 420.55 | -1.33% [-2.22%, -0.58%] | 3505036 | 3408819 | faster | -3.75% |

# Confirmation and GC sensitivity

Nine workloads were selected after the main experiment: representative regressions and a vesting improvement as a control. Selection is recorded in `followup-selection.json`.

Fresh confirmation uses 12 paired process rounds with a 100 ms sample target. Separate 4 MiB and 16 MiB nursery experiments each use eight rounds at the same target. The candidate code is identical throughout. These runs cover the selected subset, with its corresponding live input set; they do not replace the full-corpus results or establish a production GC configuration.

Changes are candidate/master elapsed time. Negative means faster. Intervals are nominal 95% paired-round bootstrap intervals. The native column pools the two complete native Criterion process pairs under their default runtime.

| Workload | Mode | Main run | Fresh confirmation [95% interval] | Native Criterion | 4 MiB nursery [95% interval] | 16 MiB nursery [95% interval] |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| marlowe/semantics/f339f59bdf92495ed2b14e2e4d3705972b4dda59aa929cffe0f1ff5355db8d79 | cek | +2.31% | +1.40% [+0.75%, +2.01%] | +2.42% | -0.00% [-0.87%, +0.82%] | +0.97% [-0.05%, +1.95%] |
| nofib/primetest/05digits | cek | +2.57% | +2.08% [+1.71%, +2.43%] | +0.19% | +2.00% [+0.86%, +3.55%] | +1.46% [-0.76%, +3.77%] |
| nofib/primetest/30digits | cek | +1.25% | +1.41% [+1.01%, +1.90%] | -2.63% | +3.60% [+0.71%, +8.15%] | +0.37% [-1.28%, +1.43%] |
| validation/coop-1 | cek | +0.85% | +2.17% [+1.78%, +2.59%] | +6.75% | +3.37% [+1.49%, +5.77%] | +1.23% [-1.44%, +2.81%] |
| validation/coop-1 | full | +2.53% | +2.30% [+1.95%, +2.64%] | +3.15% | +2.21% [+1.08%, +3.80%] | +1.07% [-0.46%, +2.06%] |
| validation/coop-2 | cek | +3.31% | +2.39% [+2.03%, +2.75%] | +9.40% | +3.34% [+1.93%, +5.65%] | +1.26% [-1.09%, +2.68%] |
| validation/coop-2 | full | -0.22% | -0.32% [-0.56%, -0.05%] | -12.25% | +0.10% [-0.79%, +1.30%] | -1.47% [-3.06%, -0.39%] |
| validation/coop-7 | cek | +3.33% | +3.55% [+3.16%, +4.13%] | +3.86% | +4.25% [+2.53%, +6.69%] | +3.38% [-0.00%, +6.56%] |
| validation/coop-7 | full | +3.21% | +3.36% [+3.18%, +3.55%] | +5.46% | +2.36% [-0.33%, +5.18%] | +2.51% [+0.40%, +3.76%] |
| validation/future-increase-margin-2 | cek | -9.20% | -9.13% [-9.35%, -8.91%] | -2.09% | -8.41% [-9.31%, -7.12%] | -9.38% [-10.42%, -8.69%] |
| validation/future-increase-margin-2 | full | +4.68% | +4.90% [+4.49%, +5.31%] | +4.54% | +4.39% [+3.62%, +5.24%] | -0.50% [-1.81%, +0.66%] |
| validation/future-settle-early-2 | cek | -8.75% | -9.09% [-9.40%, -8.78%] | +0.65% | -8.30% [-9.20%, -7.06%] | -5.97% [-10.27%, +2.08%] |
| validation/future-settle-early-2 | full | +5.27% | +4.33% [+3.70%, +4.94%] | +3.60% | +9.17% [+3.76%, +19.27%] | -2.08% [-3.19%, -1.13%] |
| validation/vesting-1 | cek | -9.69% | -9.84% [-10.21%, -9.37%] | -5.71% | -9.50% [-10.58%, -8.26%] | -10.55% [-11.68%, -9.74%] |
| validation/vesting-1 | full | -1.26% | -0.62% [-1.15%, +0.00%] | -3.75% | -1.16% [-1.74%, -0.62%] | -1.33% [-2.22%, -0.58%] |

## GC time in the fresh confirmation

| Workload | Mode | Master µs | Candidate µs | Master GC µs | Candidate GC µs | Allocation change |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| marlowe/semantics/f339f59bdf92495ed2b14e2e4d3705972b4dda59aa929cffe0f1ff5355db8d79 | cek | 2657.43 | 2694.63 | 425.48 | 436.82 | -0.20% |
| nofib/primetest/05digits | cek | 2432.71 | 2483.23 | 30.58 | 29.76 | -3.16% |
| nofib/primetest/30digits | cek | 15353.50 | 15570.96 | 160.68 | 153.05 | -2.83% |
| validation/coop-1 | cek | 118.30 | 120.87 | 4.02 | 3.78 | -3.33% |
| validation/coop-1 | full | 213.19 | 218.11 | 16.33 | 16.42 | -2.13% |
| validation/coop-2 | cek | 375.94 | 384.94 | 20.32 | 19.55 | -4.46% |
| validation/coop-2 | full | 662.31 | 660.22 | 107.82 | 106.75 | -3.18% |
| validation/coop-7 | cek | 165.65 | 171.55 | 6.34 | 5.94 | -3.23% |
| validation/coop-7 | full | 280.97 | 290.42 | 25.74 | 25.88 | -2.21% |
| validation/future-increase-margin-2 | cek | 254.80 | 231.54 | 15.36 | 14.13 | -6.04% |
| validation/future-increase-margin-2 | full | 587.32 | 616.07 | 108.92 | 140.69 | -3.31% |
| validation/future-settle-early-2 | cek | 254.35 | 231.22 | 15.33 | 14.16 | -6.04% |
| validation/future-settle-early-2 | full | 589.80 | 615.31 | 109.01 | 140.38 | -3.31% |
| validation/vesting-1 | cek | 162.85 | 146.84 | 8.13 | 7.42 | -6.34% |
| validation/vesting-1 | full | 481.14 | 478.18 | 79.10 | 77.18 | -2.75% |

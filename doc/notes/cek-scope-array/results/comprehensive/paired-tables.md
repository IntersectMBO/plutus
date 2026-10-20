# Comprehensive performance tables

Candidate: `ra-erased-context`; baseline: recorded origin/master `5d9feef021f9`.

10 adjacent paired rounds, 416 workload/mode combinations, 8320 measurements.

Negative changes mean less time or allocation. Time changes are equal-workload geometric means; allocation and summed time count one execution of each workload. Intervals bootstrap paired rounds on this fixed corpus. Per-script intervals are nominal, without a multiple-comparison correction.

## By suite

| Suite / mode | N | Time change [95% interval] | CPU time | Sum of times | Allocated bytes | Faster point estimates |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| force-delay/cek | 16 | -11.93% [-13.59%, -10.40%] | -11.92% | -10.42% | -23.55% | 16/16 |
| marlowe-rolepayout/cek | 100 | -4.46% [-4.70%, -4.24%] | -4.46% | -4.45% | -5.28% | 96/100 |
| marlowe-semantics/cek | 100 | -5.87% [-6.04%, -5.69%] | -5.87% | -1.70% | -2.53% | 91/100 |
| nofib/cek | 22 | -4.31% [-4.49%, -4.13%] | -4.32% | -4.04% | -7.43% | 18/22 |
| validation/cek | 89 | -4.96% [-5.14%, -4.76%] | -4.96% | -4.37% | -5.79% | 82/89 |
| validation/full | 89 | -1.50% [-1.63%, -1.37%] | -1.50% | -1.47% | -2.79% | 71/89 |
| all/cek | 327 | -5.40% [-5.56%, -5.24%] | -5.40% | -4.52% | -7.64% | 303/327 |

## Absolute totals and GC

Sum of mean per-evaluation times/bytes across the suite. GC shares include ordinary collections inside evaluation; forced collections between samples are excluded.

| Suite / mode | Master total ms | Candidate total ms | Master total MB | Candidate total MB | Master GC CPU share | Candidate GC CPU share |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| force-delay/cek | 52.794 | 47.295 | 203.341 | 155.461 | 64.18% | 63.21% |
| marlowe-rolepayout/cek | 6.369 | 6.086 | 70.061 | 66.365 | 4.94% | 4.84% |
| marlowe-semantics/cek | 54.447 | 53.523 | 393.938 | 383.966 | 20.95% | 21.10% |
| nofib/cek | 317.729 | 304.893 | 3350.107 | 3101.274 | 11.12% | 11.35% |
| validation/cek | 20.100 | 19.221 | 180.228 | 169.795 | 5.71% | 5.57% |
| validation/full | 55.546 | 54.732 | 373.401 | 362.968 | 20.99% | 20.77% |
| all/cek | 451.439 | 431.018 | 4197.676 | 3876.861 | 18.18% | 17.90% |

## By family

| Family / mode | N | Time change [95% interval] | Allocation |
| --- | ---: | ---: | ---: |
| force-delay/cek/nested-0 | 6 | -16.50% [-19.53%, -13.72%] | -37.91% |
| force-delay/cek/nested-1 | 5 | -11.80% [-14.24%, -9.95%] | -18.58% |
| force-delay/cek/nested-2 | 5 | -6.23% [-6.56%, -5.95%] | -15.88% |
| marlowe-rolepayout/cek/marlowe-rolepayout | 100 | -4.46% [-4.70%, -4.24%] | -5.28% |
| marlowe-semantics/cek/marlowe-semantics | 100 | -5.87% [-6.04%, -5.69%] | -2.53% |
| nofib/cek/clausify | 5 | -8.30% [-8.52%, -8.06%] | -10.93% |
| nofib/cek/knights | 3 | -5.91% [-6.02%, -5.79%] | -7.81% |
| nofib/cek/primetest | 4 | +1.30% [+0.79%, +1.85%] | -2.84% |
| nofib/cek/queens4x4 | 5 | -4.28% [-4.57%, -3.93%] | -7.69% |
| nofib/cek/queens5x5 | 5 | -3.68% [-4.10%, -3.24%] | -7.49% |
| validation/cek/auction | 9 | -3.42% [-3.69%, -3.11%] | -6.09% |
| validation/cek/coop | 7 | -0.75% [-1.31%, -0.25%] | -5.67% |
| validation/cek/crowdfunding-success | 3 | -6.99% [-10.64%, -2.83%] | -5.15% |
| validation/cek/currency | 1 | -5.07% [-5.68%, -4.65%] | -6.17% |
| validation/cek/escrow-redeem | 5 | -7.96% [-8.25%, -7.64%] | -5.94% |
| validation/cek/escrow-refund | 1 | -6.63% [-7.25%, -6.03%] | -5.64% |
| validation/cek/future-increase-margin | 5 | -7.11% [-7.40%, -6.80%] | -6.27% |
| validation/cek/future-pay-out | 4 | -7.30% [-7.54%, -7.05%] | -6.25% |
| validation/cek/future-settle-early | 4 | -7.47% [-7.72%, -7.18%] | -6.18% |
| validation/cek/game-sm-success | 10 | -2.74% [-3.02%, -2.48%] | -5.82% |
| validation/cek/guardrail | 4 | -3.39% [-3.87%, -2.92%] | -5.94% |
| validation/cek/multisig-sm | 10 | -8.90% [-9.18%, -8.62%] | -6.23% |
| validation/cek/ping-pong | 3 | -8.79% [-9.26%, -8.43%] | -6.13% |
| validation/cek/prism | 3 | -4.71% [-4.94%, -4.50%] | -5.67% |
| validation/cek/pubkey | 1 | -5.69% [-5.90%, -5.48%] | -5.00% |
| validation/cek/stablecoin | 10 | -2.31% [-2.53%, -2.11%] | -5.19% |
| validation/cek/token-account | 2 | -5.38% [-6.05%, -4.39%] | -6.01% |
| validation/cek/uniswap | 6 | -2.50% [-2.77%, -2.17%] | -5.15% |
| validation/cek/vesting | 1 | -9.69% [-10.07%, -9.20%] | -6.34% |
| validation/full/auction | 9 | -1.69% [-1.93%, -1.46%] | -2.88% |
| validation/full/coop | 7 | -0.08% [-0.27%, +0.11%] | -4.37% |
| validation/full/crowdfunding-success | 3 | -3.19% [-3.51%, -2.85%] | -1.93% |
| validation/full/currency | 1 | -1.53% [-2.16%, -0.96%] | -2.68% |
| validation/full/escrow-redeem | 5 | -1.79% [-2.03%, -1.52%] | -2.75% |
| validation/full/escrow-refund | 1 | -1.02% [-1.77%, -0.27%] | -1.44% |
| validation/full/future-increase-margin | 5 | +1.35% [+1.04%, +1.68%] | -2.92% |
| validation/full/future-pay-out | 4 | +1.65% [+1.27%, +1.98%] | -3.12% |
| validation/full/future-settle-early | 4 | +1.36% [+0.74%, +1.83%] | -2.93% |
| validation/full/game-sm-success | 10 | -1.82% [-1.98%, -1.67%] | -2.59% |
| validation/full/guardrail | 4 | -2.85% [-3.36%, -2.25%] | -4.10% |
| validation/full/multisig-sm | 10 | -0.94% [-1.16%, -0.70%] | -2.21% |
| validation/full/ping-pong | 3 | -6.04% [-7.70%, -4.98%] | -1.85% |
| validation/full/prism | 3 | -2.70% [-3.05%, -2.36%] | -2.43% |
| validation/full/pubkey | 1 | -2.43% [-2.96%, -1.92%] | -1.84% |
| validation/full/stablecoin | 10 | -3.27% [-3.50%, -3.03%] | -2.37% |
| validation/full/token-account | 2 | -2.04% [-2.60%, -1.49%] | -2.73% |
| validation/full/uniswap | 6 | -1.34% [-1.57%, -1.13%] | -3.02% |
| validation/full/vesting | 1 | -1.26% [-2.10%, -0.62%] | -2.75% |

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
| force-delay/nested-0-100k | cek | 966.78 | 764.47 | -20.92% [-22.38%, -19.86%] | 6333321 | 3933305 | faster | -27.94% |
| force-delay/nested-0-10k | cek | 68.42 | 60.75 | -11.15% [-13.72%, -8.53%] | 638053 | 398037 | faster | -10.51% |
| force-delay/nested-0-300k | cek | 5551.54 | 3834.38 | -27.90% [-40.55%, -15.24%] | 18989697 | 11789683 | faster | -12.05% |
| force-delay/nested-0-40k | cek | 301.22 | 261.76 | -13.05% [-15.35%, -10.95%] | 2536473 | 1576457 | faster | -11.76% |
| force-delay/nested-0-500k | cek | 8106.43 | 7506.88 | -7.40% [-10.31%, -3.95%] | 31645966 | 19645901 | faster | -12.83% |
| force-delay/nested-0-70k | cek | 605.41 | 502.84 | -16.92% [-18.86%, -14.97%] | 4434891 | 2754878 | faster | -16.02% |
| force-delay/nested-1-10k | cek | 256.91 | 233.32 | -9.18% [-9.71%, -8.67%] | 2587236 | 2107220 | faster | -8.05% |
| force-delay/nested-1-30k | cek | 1266.27 | 1094.48 | -13.57% [-14.17%, -12.98%] | 7751312 | 6311295 | faster | -17.92% |
| force-delay/nested-1-5k | cek | 110.07 | 102.41 | -6.96% [-7.62%, -6.37%] | 1296226 | 1056210 | faster | -5.98% |
| force-delay/nested-1-60k | cek | 4204.79 | 3237.66 | -21.47% [-31.75%, -13.25%] | 15497481 | 12617465 | faster | -5.83% |
| force-delay/nested-1-90k | cek | 6332.15 | 5891.69 | -6.95% [-7.93%, -6.08%] | 23243680 | 18923664 | faster | -8.27% |
| force-delay/nested-2-10k | cek | 538.10 | 494.88 | -8.03% [-8.37%, -7.72%] | 4536460 | 3816444 | faster | -11.55% |
| force-delay/nested-2-30k | cek | 3116.09 | 2814.82 | -9.61% [-11.34%, -8.37%] | 13599061 | 11439045 | faster | -13.31% |
| force-delay/nested-2-5k | cek | 211.05 | 199.37 | -5.53% [-5.96%, -5.07%] | 2270835 | 1910820 | faster | -8.75% |
| force-delay/nested-2-60k | cek | 7985.01 | 7721.31 | -3.30% [-4.29%, -2.34%] | 27193201 | 22873185 | faster | -10.49% |
| force-delay/nested-2-90k | cek | 13173.47 | 12573.52 | -4.55% [-5.23%, -3.70%] | 40787136 | 34307056 | faster | -5.77% |
| marlowe/rolepayout/0004000402010401030101030100040000010104020201030001000204020401 | cek | 68.03 | 65.41 | -4.26% [-5.40%, -2.69%] | 701078 | 664086 | faster | -8.20% |
| marlowe/rolepayout/0100000100010000000001000100010101000101000001000000010000010000 | cek | 90.10 | 87.38 | -3.01% [-3.36%, -2.67%] | 1032688 | 977504 | faster | -4.55% |
| marlowe/rolepayout/0101000100000101010000010101000100010101000001000001000000010101 | cek | 70.00 | 66.77 | -4.61% [-5.03%, -4.20%] | 761559 | 721855 | faster | -5.35% |
| marlowe/rolepayout/01dcc372ea619cb9f23c45b17b9a0a8a16b7ca0e04093ef8ecce291667a99a4c | cek | 57.14 | 53.48 | -6.40% [-6.93%, -5.86%] | 615253 | 582821 | faster | -7.24% |
| marlowe/rolepayout/0201020201020000020000010201020001020200000002010200000101010100 | cek | 63.51 | 59.31 | -6.61% [-7.02%, -6.20%] | 684582 | 648534 | faster | -7.98% |
| marlowe/rolepayout/0202010002010100020102020102020001010101020102010001010101000100 | cek | 56.95 | 54.51 | -4.28% [-4.63%, -3.93%] | 635317 | 601877 | faster | -6.04% |
| marlowe/rolepayout/0303020000020001010201060303040208070100050401080304020801030001 | cek | 58.97 | 56.71 | -3.83% [-4.56%, -2.78%] | 631437 | 598189 | faster | -6.97% |
| marlowe/rolepayout/031d56d71454e2c4216ffaa275c4a8b3eb631109559d0e56f44ea8489f57ba97 | cek | 71.89 | 68.01 | -5.40% [-5.74%, -5.00%] | 796287 | 755255 | faster | -5.31% |
| marlowe/rolepayout/03d730a62332c51c7b70c16c64da72dd1c3ea36c26b41cd1a1e00d39fda3d6cc | cek | 67.68 | 63.24 | -6.57% [-7.18%, -5.93%] | 738270 | 699094 | faster | -10.41% |
| marlowe/rolepayout/0403020000030204010000030001000202010101000304030001040404030100 | cek | 60.68 | 60.63 | -0.07% [-0.70%, +0.53%] | 683494 | 647678 | inconclusive | -2.85% |
| marlowe/rolepayout/0405010105020401010304080005050800040301010800080207080704020206 | cek | 68.78 | 64.02 | -6.92% [-7.45%, -6.47%] | 754510 | 715214 | faster | -7.58% |
| marlowe/rolepayout/041a2c3b111139201a3a2c173c392b170e16370d300f2d28342d0f2f0e182e01 | cek | 68.27 | 64.94 | -4.87% [-5.71%, -4.09%] | 764430 | 724062 | faster | -8.05% |
| marlowe/rolepayout/04f592afc6e57c633b9c55246e7c82e87258f04e2fb910c37d8e2417e9db46e5 | cek | 82.27 | 79.50 | -3.79% [-7.01%, +2.42%] | 908312 | 860360 | inconclusive | -6.42% |
| marlowe/rolepayout/057ebc80922f16a5f4bf13e985bf586b8cff37a2f6fe0f3ce842178c16981027 | cek | 57.60 | 54.26 | -5.79% [-6.25%, -5.32%] | 624518 | 591518 | faster | -5.36% |
| marlowe/rolepayout/06317060a8e488b1219c9dae427f9ce27918a9e09ee8ac424afa33ca923f7954 | cek | 61.27 | 57.94 | -5.43% [-5.95%, -4.96%] | 675358 | 639934 | faster | -4.75% |
| marlowe/rolepayout/07658a6c898ad6d624c37df1e49e909c2e9349ba7f4c0a6be5f166fe239bfcae | cek | 54.09 | 53.14 | -1.75% [-2.25%, -1.25%] | 597701 | 566165 | faster | -1.47% |
| marlowe/rolepayout/0bdca1cb8fa7e38e09062557b82490714052e84e2054e913092cd84ac071b961 | cek | 67.04 | 64.44 | -3.87% [-4.58%, -3.22%] | 763606 | 723358 | faster | -0.58% |
| marlowe/rolepayout/0c9d3634aeae7038f839a1262d1a8bc724dc77af9426459417a56ec73240f0e0 | cek | 61.33 | 56.72 | -7.51% [-7.78%, -7.26%] | 668806 | 633806 | faster | +18.61% |
| marlowe/rolepayout/0d0f01050a0a0a0b0b050d0404090e0d0506000d0a041003040e0f100e0a0408 | cek | 60.01 | 57.26 | -4.58% [-4.97%, -4.15%] | 678869 | 642646 | faster | +21.81% |
| marlowe/rolepayout/0dbb692d2bf22d25eeceac461cfebf616f54003077a8473abc0457f18e025960 | cek | 71.76 | 66.51 | -7.32% [-7.71%, -6.94%] | 785519 | 744135 | faster | +19.79% |
| marlowe/rolepayout/0e00171d0f1e1f14070d0a00091f07101808021d081e1b120219081312081e15 | cek | 60.00 | 55.85 | -6.91% [-7.57%, -6.24%] | 645349 | 611637 | faster | +15.21% |
| marlowe/rolepayout/0e72f62b0f922e31a2340baccc768104025400cf7fdd7dae62fbba5fc770936d | cek | 65.26 | 63.58 | -2.56% [-3.10%, -1.94%] | 717367 | 679791 | faster | +24.14% |
| marlowe/rolepayout/0e97c9d9417354d9460f2eb35018d3904b7b035af16ab299258adab93be0911a | cek | 64.12 | 60.44 | -5.74% [-6.14%, -5.33%] | 701078 | 664086 | faster | +15.57% |
| marlowe/rolepayout/0f010d040810040b10020e040f0e030b0a0d100f0c080c0c05000d04100c100f | cek | 68.59 | 62.45 | -8.96% [-9.37%, -8.52%] | 742846 | 703350 | faster | +4.36% |
| marlowe/rolepayout/1138a04a83edc0579053f9ffa9394b41df38230121fbecebee8c039776a88c0c | cek | 59.21 | 54.77 | -7.48% [-8.19%, -6.95%] | 629221 | 595909 | faster | +11.76% |
| marlowe/rolepayout/121a0a1b12030616111f02121a0e070716090a0e031c071419121f141409031d | cek | 57.93 | 54.46 | -5.98% [-6.37%, -5.62%] | 623726 | 590854 | faster | +23.06% |
| marlowe/rolepayout/159e5a1bf16fe984b5569be7011b61b5e98f5d2839ca7e1b34c7f2afc7ffb58e | cek | 57.48 | 56.34 | -2.00% [-2.76%, -0.98%] | 633829 | 600389 | faster | +7.76% |
| marlowe/rolepayout/195f522b596360690d04586a2563470f2214163435331a6622311f7323433f1c | cek | 57.25 | 54.14 | -5.44% [-5.77%, -5.10%] | 620637 | 587829 | faster | -6.49% |
| marlowe/rolepayout/1a20b465d48a585ffd622bd8dc26a498a3c12f930ab4feab3a5064cfb3bc536a | cek | 64.71 | 60.50 | -6.51% [-6.94%, -6.04%] | 696782 | 660166 | faster | -8.67% |
| marlowe/rolepayout/211e1b6c10260c4620074d2e372c260d38643a3d605f63772524034f0a4a7632 | cek | 61.50 | 56.43 | -8.25% [-8.76%, -7.77%] | 664582 | 629702 | faster | -8.03% |
| marlowe/rolepayout/21a1426fb3fb3019d5dc93f210152e90b0a6e740ef509b1cdd423395f010e0ca | cek | 65.86 | 60.49 | -8.16% [-8.84%, -7.35%] | 709070 | 671438 | faster | -8.65% |
| marlowe/rolepayout/224ce46046fab9a17be4197622825f45cc0c59a6bd1604405148e43768c487ef | cek | 59.04 | 54.89 | -7.01% [-7.45%, -6.54%] | 629221 | 595909 | faster | -8.04% |
| marlowe/rolepayout/332c2b1c11383d1b373e1315201f1128010e0e1518332f273f141b23243f2a07 | cek | 55.78 | 52.55 | -5.79% [-6.27%, -5.28%] | 613653 | 581285 | faster | -6.66% |
| marlowe/rolepayout/3565ee025317e065e8555eef288080276716366769aad89e03389f5ec4ce26d7 | cek | 60.66 | 58.90 | -2.89% [-3.52%, -2.31%] | 675270 | 639662 | faster | -5.31% |
| marlowe/rolepayout/3569299fc986f5354d02e627a9eaa48ab46d5af52722307a0af72bae87e256dc | cek | 57.68 | 54.11 | -6.19% [-6.70%, -5.69%] | 624517 | 591517 | faster | +9.89% |
| marlowe/rolepayout/36866914aa07cf62ef36cf2cd64c7f240e3371e27bb9fff5464301678e809c40 | cek | 57.27 | 54.09 | -5.55% [-6.03%, -4.99%] | 624517 | 591517 | faster | +1.64% |
| marlowe/rolepayout/371c10d2526fc0f09dbe9ed59e44dcd949270b27dc42035addd7ff9f7e0d05e7 | cek | 70.30 | 66.04 | -6.07% [-6.41%, -5.74%] | 769814 | 729270 | faster | +13.82% |
| marlowe/rolepayout/3897ef714bba3e6821495b706c75f8d64264c3fdaa58a3826c808b5a768c303d | cek | 59.75 | 56.60 | -5.27% [-5.77%, -4.77%] | 654190 | 619526 | faster | +12.52% |
| marlowe/rolepayout/4121d88f14387d33ac5e1329618068e3848445cdd66b29e5ba382be2e02a174a | cek | 70.59 | 64.57 | -8.53% [-9.06%, -8.03%] | 771647 | 730679 | faster | -3.94% |
| marlowe/rolepayout/4299c7fcf093a5dbfe114c188e32ca199b571a7c25cb7f766bf49f12dab308be | cek | 63.76 | 60.73 | -4.74% [-5.38%, -4.03%] | 701078 | 664086 | faster | +13.63% |
| marlowe/rolepayout/452e17d16222a427707fa83f63ffb79f606cc25c755a18b1e3274c964ed5ec99 | cek | 68.15 | 66.43 | -2.52% [-3.45%, -1.75%] | 781286 | 740662 | faster | -3.61% |
| marlowe/rolepayout/46f8d00030436e4da490a86b331fa6c3251425fb8c19556080e124d75bad7bd6 | cek | 56.43 | 56.63 | +0.32% [-0.87%, +2.16%] | 629949 | 596701 | inconclusive | -0.18% |
| marlowe/rolepayout/47364cfaf2c00f7d633283dce6cf84e4fd4e8228c0a0aa50e7c55f35c3ecaa1c | cek | 56.63 | 56.33 | -0.52% [-0.93%, -0.10%] | 629949 | 596702 | faster | -1.51% |
| marlowe/rolepayout/49b8275d0cb817be40865694ab05e3cfe5fc35fb43b78e7de68c1f3519b536bd | cek | 61.30 | 58.57 | -4.45% [-5.07%, -3.85%] | 668286 | 633118 | faster | -6.26% |
| marlowe/rolepayout/4dd7755b6ca1f0c9747c1fc0ee4da799f6f1c07108e980bd9f820911ad711ff2 | cek | 79.18 | 75.96 | -4.07% [-4.39%, -3.76%] | 884600 | 838136 | faster | -4.38% |
| marlowe/rolepayout/4fbcfdb577a56b842d6f6938187a783f71d9da7519353e3da3ef0c564e1eb344 | cek | 72.12 | 69.17 | -4.10% [-4.42%, -3.81%] | 809087 | 766751 | faster | -4.19% |
| marlowe/rolepayout/5a0725d49c733130eda8bc6ed5234f7f6ff8c9dd2d201e8806125e5fbcc081f9 | cek | 62.81 | 59.57 | -5.15% [-5.54%, -4.78%] | 684782 | 648670 | faster | -5.60% |
| marlowe/rolepayout/5a2aae344e569a2c644dd9fa8c7b1f129850937eb562b7748c275f9e40bed596 | cek | 56.27 | 56.27 | -0.00% [-0.34%, +0.33%] | 629949 | 596701 | inconclusive | -3.51% |
| marlowe/rolepayout/5ade103e9530dd0d572fe1b053ea65ad925c6ebbe321e873ace8b804363fa82c | cek | 81.00 | 77.88 | -3.86% [-4.38%, -3.41%] | 931175 | 881383 | faster | -7.49% |
| marlowe/rolepayout/5d4c62a0671c65a14f6a15093e3efc4f1816d95a5a58fd92486bedaae8d9526b | cek | 70.48 | 64.69 | -8.21% [-8.59%, -7.82%] | 763606 | 723358 | faster | -9.87% |
| marlowe/rolepayout/5efe992e306e31cc857c64a62436ad2f9325acc5b4a74a8cebccdfd853ce63d2 | cek | 61.68 | 58.95 | -4.43% [-4.76%, -4.09%] | 668285 | 633117 | faster | -4.59% |
| marlowe/rolepayout/622a7f3bc611b5149253c9189da022a9ff296f60a5b7c172a6dc286faa7284fa | cek | 70.21 | 66.43 | -5.38% [-5.68%, -5.04%] | 788687 | 746919 | faster | -6.35% |
| marlowe/rolepayout/6621a69217f09d91f42876a9c0cecf79de0e29bdd5b16c82c6c52cf959092ec4 | cek | 64.02 | 59.96 | -6.35% [-6.73%, -5.87%] | 708310 | 670446 | faster | -6.38% |
| marlowe/rolepayout/674b0577409957172ad85223c765d17e94c27714276c49c38dfae0a47a561a1e | cek | 57.49 | 54.68 | -4.90% [-5.71%, -3.79%] | 620637 | 587829 | faster | -5.82% |
| marlowe/rolepayout/6b7bc2b9002a71b33cfd535d43f26334a283d0b9ad189b7cd74baac232c3b9fc | cek | 54.10 | 53.17 | -1.71% [-2.16%, -1.23%] | 597701 | 566165 | faster | -3.60% |
| marlowe/rolepayout/6c364699767a84059ffd99cf718562a8c09d96e343f23dc481e8ffda13af424f | cek | 56.65 | 59.40 | +3.72% [-1.42%, +14.16%] | 629950 | 596702 | inconclusive | -3.36% |
| marlowe/rolepayout/6d66bddb4269bdf77392d3894da5341cf019d39787522af4f83f01285991e93c | cek | 57.25 | 56.49 | -1.33% [-2.31%, -0.03%] | 633829 | 600389 | faster | +2.00% |
| marlowe/rolepayout/73f044f34a30f26639c58bafe952047f74c7bf1eafebab5aadf5b73cfb9024ed | cek | 56.42 | 59.03 | +3.67% [-1.18%, +13.24%] | 629950 | 596702 | inconclusive | +12.14% |
| marlowe/rolepayout/7b1dd76edc27f00eb382bf996378155baf74d6a7c6f3d5ec837c39d29784aade | cek | 57.39 | 56.18 | -2.11% [-2.45%, -1.80%] | 633829 | 600389 | faster | -3.29% |
| marlowe/rolepayout/803eae94d62e2afc0e835c204af8362170301bc329e2d849d5f5a47dddf479ec | cek | 67.91 | 64.25 | -5.39% [-5.91%, -4.86%] | 745110 | 705222 | faster | -5.69% |
| marlowe/rolepayout/87167fc5469adac97c1be749326fa79a6b7862ce68aa4abcb438e3c034bd0899 | cek | 66.99 | 65.63 | -2.03% [-2.50%, -1.53%] | 779910 | 739094 | faster | -3.29% |
| marlowe/rolepayout/8c0fa5d9d6724c5c72c67e055d4bfc36a385ded7c3c81c08cdbd8705829af6e6 | cek | 70.45 | 68.10 | -3.34% [-3.82%, -2.89%] | 782775 | 740967 | faster | -3.14% |
| marlowe/rolepayout/962c2c658b19904372984a56409707401e64e9b03c1986647134cfd329ec5139 | cek | 63.40 | 59.90 | -5.51% [-6.08%, -4.95%] | 701326 | 663902 | faster | -7.07% |
| marlowe/rolepayout/996804e90f2c75fe68886fc8511304b8ab9b36785f8858f5cb098e91c159dde9 | cek | 58.94 | 55.90 | -5.15% [-5.69%, -4.66%] | 655269 | 620829 | faster | -9.12% |
| marlowe/rolepayout/a004a989c005d59043f996500e110fa756ad1b85800b889d5815a0106388e1d7 | cek | 63.56 | 57.55 | -9.46% [-9.99%, -8.93%] | 678390 | 642238 | faster | -13.63% |
| marlowe/rolepayout/a0fba5740174b5cd24036c8b008cb1efde73f1edae097b9325c6117a0ff40d3b | cek | 66.74 | 61.12 | -8.43% [-8.83%, -7.99%] | 716743 | 678823 | faster | -10.16% |
| marlowe/rolepayout/a1b25347409c3993feca1a60b6fcaf93d1d4bbaae19ab06fdf50cedc26cee68d | cek | 56.72 | 52.95 | -6.65% [-7.03%, -6.24%] | 611373 | 579133 | faster | -5.38% |
| marlowe/rolepayout/a27524cfad019df45e4e8316f927346d4cc39da6bdd294fb2c33c3f58e6a8994 | cek | 56.28 | 56.16 | -0.21% [-0.69%, +0.22%] | 629950 | 596702 | inconclusive | -0.68% |
| marlowe/rolepayout/a6664a2d2a82f370a34a36a45234f6b33120a39372331678a3b3690312560ce9 | cek | 73.65 | 69.02 | -6.30% [-6.55%, -6.03%] | 809663 | 766431 | faster | -6.90% |
| marlowe/rolepayout/a6f064b83b31032ea7f25921364727224707268e472a569f584cc6b1d8c017e8 | cek | 57.18 | 56.12 | -1.86% [-2.34%, -1.37%] | 633830 | 600390 | faster | -5.30% |
| marlowe/rolepayout/a7cb09f417c3f089619fe25b7624392026382b458486129efcff18f8912bf302 | cek | 56.43 | 56.11 | -0.57% [-1.23%, +0.04%] | 629949 | 596701 | inconclusive | -1.79% |
| marlowe/rolepayout/a92b4072cb8601fa697e1150c08463b14ffced54eb963df08d322216e27373cb | cek | 57.51 | 56.14 | -2.37% [-2.98%, -1.77%] | 633829 | 600389 | faster | -3.04% |
| marlowe/rolepayout/af2e072b5adfaa7211e0b341e1f7319c4f4e7364a4247c9247132a927e914753 | cek | 68.61 | 65.12 | -5.07% [-5.73%, -4.40%] | 768327 | 727783 | faster | -7.07% |
| marlowe/rolepayout/b43564af5f13cc5208b92b1ad6d45369446f378d3891e5cb3e353b30d4f3fb10 | cek | 57.07 | 57.27 | +0.12% [-2.14%, +4.31%] | 633830 | 600390 | inconclusive | -3.40% |
| marlowe/rolepayout/b6243a5b4c353ce4852aa41705111d57867d2783eeef76f6d59beb2360da6e90 | cek | 80.37 | 78.00 | -2.94% [-3.37%, -2.54%] | 884647 | 838623 | faster | -3.12% |
| marlowe/rolepayout/b869f3928200061abb1c3060425b9354b0e08cbf4400b340b8707c14b34317cd | cek | 87.94 | 85.92 | -2.30% [-2.76%, -1.83%] | 989810 | 937978 | faster | -3.76% |
| marlowe/rolepayout/bcdbc576d63b0454100ad06893812edafc2e7e4934fec1b44e2d06eb34f36eb8 | cek | 57.35 | 56.12 | -2.14% [-2.77%, -1.55%] | 633829 | 600389 | faster | -1.28% |
| marlowe/rolepayout/bd460b7549b70c52e37b312a4242041eac18fe4a266f018bcea0c78a9085a271 | cek | 66.28 | 65.45 | -1.24% [-1.98%, -0.48%] | 752030 | 712366 | faster | +3.16% |
| marlowe/rolepayout/bd79f4a84db23b7c4cd219d498bd581e085cbc3437957e74a8862281a700700b | cek | 68.43 | 66.64 | -3.70% [-7.92%, +4.93%] | 742942 | 703446 | inconclusive | -8.77% |
| marlowe/rolepayout/c11490431db3a92efdda70933ba411a0423935e73a75c856e326dbcf6672f3bf | cek | 59.52 | 54.56 | -8.35% [-8.73%, -7.96%] | 635317 | 601877 | faster | -9.11% |
| marlowe/rolepayout/c4d4c88c5fe378a25a034025994a0d0b1642f10c8e6e513f872327fa895bfc7e | cek | 62.05 | 60.71 | -2.17% [-2.55%, -1.76%] | 694342 | 657358 | faster | -3.44% |
| marlowe/rolepayout/c78eeba7681d2ab51b4758efa4c812cc041928837c6e7563d8283cce67ce2e02 | cek | 63.35 | 60.27 | -4.86% [-5.27%, -4.40%] | 689486 | 653062 | faster | -6.09% |
| marlowe/rolepayout/c99ecc2146ce2066ba6dffc734923264f8794815acbc2ec74c2c2c42ba272e4d | cek | 74.10 | 70.73 | -4.55% [-4.95%, -4.19%] | 810487 | 767135 | faster | -4.93% |
| marlowe/rolepayout/caa409c40e39aed9b0f59214b4baa178c375526dea6026b4552b88d2cc729716 | cek | 54.03 | 53.16 | -1.61% [-2.07%, -1.19%] | 597701 | 566165 | faster | -3.33% |
| marlowe/rolepayout/cb2ab8e22d1f64e8d204dece092e90e9bf1fa8b2a6e9cba5012dbe4978065832 | cek | 56.89 | 54.45 | -4.30% [-4.81%, -3.77%] | 635318 | 601877 | faster | -12.08% |
| marlowe/rolepayout/cc1e82927f6c65b3e912200ae30588793d2066e1d4a6627c21955944ac9bd528 | cek | 67.17 | 64.52 | -3.97% [-5.17%, -2.17%] | 726151 | 688383 | faster | -4.50% |
| marlowe/rolepayout/d5cda74eb0947e025e02fb8ed365df39d0a43e4b42cd3573ac2d8fcb29115997 | cek | 65.67 | 62.73 | -4.48% [-5.30%, -3.59%] | 709047 | 671455 | faster | -5.66% |
| marlowe/rolepayout/d6bc8ac4155e22300085784148bbc9d9bbfea896e1009dd396610a90e3943032 | cek | 66.96 | 65.38 | -2.36% [-2.81%, -1.90%] | 752031 | 712366 | faster | -3.26% |
| marlowe/rolepayout/da353bf9219801fa1bf703fc161497570954e9af7e10ffe95c911a9ef97e77bd | cek | 62.28 | 57.06 | -8.38% [-8.90%, -7.79%] | 668246 | 633262 | faster | -8.53% |
| marlowe/rolepayout/dc45c5f1b700b1334db99f50823321daaef0e6925b9b2fabbc9df7cde65af62e | cek | 59.47 | 57.72 | -2.95% [-3.53%, -2.44%] | 659381 | 624789 | faster | -4.31% |
| marlowe/rolepayout/df487b2fd5c1583fa33644423849bc1ab5f02f37edc0c235f34ef01cb12604f6 | cek | 61.64 | 56.73 | -7.97% [-8.31%, -7.66%] | 660870 | 626279 | faster | -9.13% |
| marlowe/rolepayout/eabeeae18131af89fa57936c0e9eb8d2c7adba534f7e1a517d75410028fa0d6c | cek | 57.65 | 56.09 | -2.68% [-3.73%, -1.93%] | 633829 | 600389 | faster | -3.25% |
| marlowe/rolepayout/ec4712ee820eb959a43ebedfab6735f2325fa52994747526ffd2a4f4f84dd58e | cek | 67.17 | 62.72 | -6.62% [-6.90%, -6.34%] | 733846 | 695702 | faster | -7.13% |
| marlowe/rolepayout/ee3962fbd7373360f46decef3c9bda536a0b1daf6cda3b8a4bcfd6deeb5b4c53 | cek | 68.40 | 63.05 | -7.81% [-8.10%, -7.51%] | 742942 | 703446 | faster | -9.07% |
| marlowe/rolepayout/f1a1e6a487f91feca5606f72bbb1e948c71abf043c6a0ea83bfea9ec6a0f08d8 | cek | 56.50 | 56.03 | -0.83% [-1.39%, -0.26%] | 629950 | 596703 | faster | -3.41% |
| marlowe/rolepayout/f2932e4ca4bbb94b0a9ffbe95fcb7bd5639d9751d75d56d5e14efa5bbed981df | cek | 57.25 | 54.34 | -5.08% [-5.66%, -4.47%] | 624518 | 591518 | faster | -7.74% |
| marlowe/rolepayout/f53e8cafe26647ccce51e4c31db13608aea1f39034c0f52dee2e5634ef66e747 | cek | 64.64 | 60.23 | -6.83% [-7.34%, -6.32%] | 696470 | 659606 | faster | -8.07% |
| marlowe/rolepayout/f7275afb60e33a550df13a132102e7e925dd28965a4efbe510a89b077ff9417f | cek | 57.16 | 56.06 | -1.92% [-2.29%, -1.54%] | 633829 | 600389 | faster | -3.28% |
| marlowe/rolepayout/fc8c5f45ffcdb024c21e0f34b22c23de8045a94d5e1a5bda1555c45ddb059f82 | cek | 61.51 | 56.43 | -8.26% [-8.55%, -7.98%] | 664581 | 629701 | faster | -8.74% |
| marlowe/rolepayout/ff38b1ec89952d0247630f107a90cbbeb92ecbfcd19b284f60255718e4ec7548 | cek | 70.05 | 67.39 | -3.79% [-4.07%, -3.55%] | 775294 | 734294 | faster | -6.14% |
| marlowe/semantics/0000020002010200020101020201000100010001020101020201010000020102 | cek | 112.55 | 102.08 | -9.30% [-9.55%, -9.09%] | 1008243 | 953771 | faster | -11.94% |
| marlowe/semantics/0001000101000000010101000001000001010101010100000001000001010000 | cek | 163.84 | 157.23 | -4.07% [-5.29%, -2.05%] | 1509191 | 1445711 | faster | -6.96% |
| marlowe/semantics/0003040402030103010203030303000200000104030002040304020400000102 | cek | 343.97 | 340.15 | -1.10% [-2.00%, -0.50%] | 3172672 | 3003824 | faster | -4.43% |
| marlowe/semantics/004025fd712d6c325ffa12c16d157064192992faf62e0b991d7310a2f91666b8 | cek | 278.37 | 271.99 | -2.29% [-2.62%, -2.00%] | 2509123 | 2396195 | faster | -4.29% |
| marlowe/semantics/0101010001010101010101000100010100000001010000010001000001000101 | cek | 414.28 | 422.16 | +1.90% [+1.52%, +2.31%] | 3718239 | 3637463 | slower | -0.56% |
| marlowe/semantics/0101020201010201010200010102000201000201010102000102010201010000 | cek | 104.53 | 93.59 | -10.47% [-10.80%, -10.12%] | 939969 | 888041 | faster | -11.93% |
| marlowe/semantics/0101080808040600020306010000000302050807010208060100070207080202 | cek | 261.04 | 245.34 | -6.02% [-6.40%, -5.67%] | 2479526 | 2356967 | faster | -8.08% |
| marlowe/semantics/0104010200020000040103020102020004040300030304040400010301040303 | cek | 265.22 | 243.17 | -8.31% [-8.83%, -7.84%] | 2413031 | 2290247 | faster | -10.38% |
| marlowe/semantics/04000f0b04051006000e060f09080d0b090d0104050a0b0f0506070f0a070008 | cek | 252.08 | 250.27 | -0.72% [-1.14%, -0.08%] | 2309831 | 2201359 | faster | -3.48% |
| marlowe/semantics/0543a00ba1f63076c1db6bf94c6ff13ae7d266dd7544678743890b0e8e1add63 | cek | 362.26 | 364.59 | +0.64% [+0.35%, +0.95%] | 3437436 | 3290396 | slower | -1.08% |
| marlowe/semantics/0705030002040601010206030604080208020207000101060706050502040301 | cek | 373.51 | 361.39 | -3.20% [-5.36%, -1.83%] | 3472442 | 3350226 | faster | +0.92% |
| marlowe/semantics/07070c070510030509010e050d00040907050e0a0d06030f1006030701020607 | cek | 347.94 | 328.39 | -5.62% [-5.88%, -5.36%] | 3167991 | 3003831 | faster | -7.95% |
| marlowe/semantics/0bcfd9487614104ec48de2ea0b2c0979866a95115748c026f9ec129384c262c4 | cek | 385.81 | 369.58 | -4.21% [-4.54%, -3.91%] | 3534745 | 3360841 | faster | -6.13% |
| marlowe/semantics/0be82588e4e4bf2ef428d2f44b7687bbb703031d8de696d90ec789e70d6bc1d8 | cek | 472.38 | 474.08 | +0.36% [+0.08%, +0.67%] | 4376950 | 4163985 | slower | -2.33% |
| marlowe/semantics/0f1d0110001b121d051e15140c0c05141d151c1f1d201c040f10091b020a0e1a | cek | 162.98 | 145.21 | -10.90% [-11.26%, -10.49%] | 1497854 | 1417614 | faster | -13.18% |
| marlowe/semantics/119fbea4164e2bf21d2b53aa6c2c4e79414fe55e4096f5ce2e804735a7fbaf91 | cek | 255.52 | 245.56 | -3.90% [-4.28%, -3.49%] | 2313919 | 2201143 | faster | -6.36% |
| marlowe/semantics/12910f24d994d451ff379b12c9d1ecdb9239c9b87e5d7bea570087ec506935d5 | cek | 167.69 | 152.43 | -9.10% [-9.45%, -8.70%] | 1568677 | 1486669 | faster | -11.46% |
| marlowe/semantics/18cefc240debc0fcab14efdd451adfd02793093efe7bc76d6322aed6ddb582ad | cek | 251.62 | 247.83 | -1.51% [-1.75%, -1.24%] | 2313161 | 2191057 | faster | -3.75% |
| marlowe/semantics/1a2f2540121f09321216090b2b1f211e3f020c2c133a1a3c3f3c232a26153a04 | cek | 105.75 | 93.28 | -11.78% [-12.70%, -11.02%] | 945817 | 893689 | faster | -11.71% |
| marlowe/semantics/1a573aed5c46d637919ccb5548dfc22a55c9fc38298d567d15ee9f2eea69d89e | cek | 311.13 | 308.76 | -0.76% [-1.24%, -0.29%] | 2979223 | 2835605 | faster | -3.59% |
| marlowe/semantics/1d56060c3b271226064c672a282663643b1b0823471c67737f0b076870331260 | cek | 278.46 | 273.65 | -1.72% [-2.55%, -1.05%] | 2517986 | 2408594 | faster | -4.93% |
| marlowe/semantics/1d6e3c137149a440f35e0efc685b16bfb8052ebcf66ec4ad77e51c11501381c7 | cek | 104.58 | 93.39 | -10.70% [-11.01%, -10.40%] | 945817 | 893689 | faster | -13.99% |
| marlowe/semantics/1f0f02191604101e1f201016171604060d010d1d1c150e110a110e1006160a0d | cek | 554.38 | 558.02 | +0.65% [+0.15%, +1.14%] | 5110576 | 5063791 | slower | -0.74% |
| marlowe/semantics/202d273721330b31193405101e0637202e2a0f1140211c3e3f171e26312b0220 | cek | 3169.06 | 3156.82 | -0.39% [-1.03%, +0.38%] | 19440803 | 19379083 | inconclusive | +2.02% |
| marlowe/semantics/21953bf8798b28df60cb459db24843fb46782b19ba72dc4951941fb4c20d2263 | cek | 122.52 | 108.12 | -11.75% [-12.12%, -11.41%] | 1120714 | 1061082 | faster | -14.05% |
| marlowe/semantics/238b21364ab5bdae3ddb514d7001c8feba128b4ddcf426852b441f9a9d02c882 | cek | 104.28 | 97.80 | -6.89% [-10.49%, +0.49%] | 939971 | 888043 | inconclusive | -11.46% |
| marlowe/semantics/26e24ee631a6d927ea4fb4fac530cfd82ff7636986014de2d2aaa460ddde0bc3 | cek | 191.28 | 168.52 | -11.90% [-12.16%, -11.63%] | 1694352 | 1601312 | faster | -14.35% |
| marlowe/semantics/2797d7ac77c1b6aff8e42cf9a47fa86b1e60f22719a996871ad412cbe4de78b5 | cek | 1061.17 | 1080.30 | +1.80% [+0.80%, +2.59%] | 9917467 | 9855795 | slower | -1.93% |
| marlowe/semantics/28fdce478e179db0e38fb5f3f4105e940ece450b9ce8a0f42a6e313b752e6f2c | cek | 370.18 | 371.18 | +0.27% [-0.23%, +0.75%] | 3337203 | 3234083 | inconclusive | -1.81% |
| marlowe/semantics/2cb21612178a2d9336b59d06cbf80488577463d209a453048a66c6eee624a695 | cek | 265.69 | 254.47 | -4.22% [-4.55%, -3.85%] | 2413322 | 2290689 | faster | -6.10% |
| marlowe/semantics/2f58c9d884813042bce9cf7c66048767dff166785e8b5183c8139db2aa7312d1 | cek | 277.69 | 268.58 | -3.28% [-3.67%, -2.96%] | 2567811 | 2449819 | faster | -6.87% |
| marlowe/semantics/30aa34dfbe89e0c43f569929a96c0d2b74c321d13fec0375606325eee9a34a6a | cek | 386.34 | 380.51 | -2.43% [-6.72%, +6.32%] | 3504888 | 3323718 | inconclusive | -8.63% |
| marlowe/semantics/322acde099bc34a929182d5b894214fc87ec88446e2d10625119a9d17fa3ec3d | cek | 104.88 | 94.06 | -10.32% [-10.81%, -9.69%] | 945818 | 893690 | faster | -13.13% |
| marlowe/semantics/331e4a1bb30f28d7073c54f9a13c10ae19e2e396c299a0ce101ee6bf4b2020db | cek | 157.84 | 141.03 | -10.65% [-11.31%, -10.04%] | 1460093 | 1381837 | faster | -12.83% |
| marlowe/semantics/33c3efd79d9234a78262b52bc6bbf8124cb321a467dedb278328215167eca455 | cek | 208.51 | 196.02 | -5.99% [-6.20%, -5.76%] | 1950730 | 1847642 | faster | -8.29% |
| marlowe/semantics/383683bfcecdab0f4df507f59631c702bd11a81ca3841f47f37633e8aacbb5de | cek | 261.94 | 239.08 | -8.72% [-9.12%, -8.31%] | 2352013 | 2234605 | faster | -13.20% |
| marlowe/semantics/3bb75b2e53eb13f718eacd3263ab4535f9137fabffc9de499a0de7cabb335479 | cek | 104.50 | 93.84 | -10.20% [-10.52%, -9.93%] | 939968 | 888040 | faster | -13.34% |
| marlowe/semantics/3db496e6cd39a8b888a89d0de07dace4397878958cab3b9d9353978b08c36d8a | cek | 282.67 | 268.54 | -5.00% [-5.56%, -4.22%] | 2573081 | 2454609 | faster | -7.90% |
| marlowe/semantics/44a9e339fa25948b48637fe7e10dcfc6d1256319a7b5ce4202cb54dfef8e37e7 | cek | 104.66 | 93.98 | -10.21% [-10.58%, -9.85%] | 939968 | 888040 | faster | -10.41% |
| marlowe/semantics/4c3efd13b6c69112a8a888372d56c86e60c232125976f29b1c3e21d9f537845c | cek | 345.65 | 330.63 | -4.22% [-7.28%, -2.41%] | 3220009 | 3053127 | faster | -7.89% |
| marlowe/semantics/4d7adf91bfc93cebe95a7e054ec17cfbb912b32bd8aecb48a228b50e02b055c8 | cek | 232.10 | 226.18 | -2.58% [-3.61%, -0.92%] | 2178603 | 2066203 | faster | -7.84% |
| marlowe/semantics/4f9e8d361b85e62db2350dd3ae77463540e7af0d28e1eb68faeecc45f4655f57 | cek | 144.60 | 133.59 | -7.62% [-7.99%, -7.18%] | 1322739 | 1262491 | faster | -9.60% |
| marlowe/semantics/52df7c8dfaa5f801cd837faa65f2fd333665fff00a555ce8c55e36ddc003007a | cek | 129.44 | 113.71 | -12.13% [-13.39%, -11.38%] | 1145963 | 1088339 | faster | -14.02% |
| marlowe/semantics/53ed4db7ab33d6f907eec91a861d1188269be5ae1892d07ee71161bfb55a7cb7 | cek | 130.05 | 115.97 | -10.83% [-11.13%, -10.52%] | 1172186 | 1114090 | faster | -13.64% |
| marlowe/semantics/55dfe42688ad683b638df1fa7700219f00f53b335a85a2825502ab1e0687197e | cek | 104.93 | 94.04 | -10.39% [-10.99%, -9.74%] | 939969 | 888041 | faster | -15.43% |
| marlowe/semantics/56333d4e413dbf1a665463bf68067f63c118f38f7539b7ba7167d577c0c8b8ce | cek | 254.17 | 232.79 | -8.41% [-8.77%, -8.03%] | 2372505 | 2246859 | faster | -10.12% |
| marlowe/semantics/57728d8b19b0e06412786f3dfed9e1894cd0ad1d2bc2bd497ec0ecb68f989d2b | cek | 105.12 | 93.84 | -10.73% [-11.62%, -10.01%] | 939969 | 888041 | faster | -11.27% |
| marlowe/semantics/5abae75af26f45658beccbe48f7c88e74efdfc0b8409ba1e98f95fa5b6caf999 | cek | 165.26 | 147.98 | -10.46% [-10.72%, -10.20%] | 1536479 | 1454958 | faster | -12.06% |
| marlowe/semantics/5d0a88250f13c49c20e146819357a808911c878a0e0a7d6f7fe1d4a619e06112 | cek | 373.75 | 353.27 | -4.33% [-13.03%, +0.49%] | 3262600 | 3110672 | inconclusive | -1.39% |
| marlowe/semantics/5e274e0f593511543d41570a4b03646c1d7539062b5728182e073e5760561a66 | cek | 342.72 | 329.27 | -3.93% [-4.16%, -3.66%] | 3210695 | 3047287 | faster | -6.08% |
| marlowe/semantics/5e2c68ac9f62580d626636679679b97109109df7ac1a8ce86d3e43dfb5e4f6bc | cek | 177.08 | 159.22 | -10.08% [-11.07%, -9.43%] | 1625696 | 1540040 | faster | -12.42% |
| marlowe/semantics/5f130d19918807b60eab4c03119d67878fb6c6712c28c54f5a25792049294acc | cek | 104.61 | 93.65 | -10.48% [-10.79%, -10.19%] | 945816 | 893688 | faster | -12.79% |
| marlowe/semantics/5f306b4b24ff2b39dab6cdc9ac6ca9bb442c1dc6f4e7e412eeb5a3ced42fb642 | cek | 252.68 | 231.70 | -8.30% [-8.52%, -8.10%] | 2279215 | 2161856 | faster | -9.97% |
| marlowe/semantics/5f3d46c57a56cef6764f96c9de9677ac6e494dd7a4e368d1c8dd9c1f7a4309a5 | cek | 168.21 | 148.90 | -11.48% [-11.67%, -11.27%] | 1545528 | 1463816 | faster | -13.59% |
| marlowe/semantics/64c3d5b43f005855ffc4d0950a02fd159aa1575294ea39061b81a194ebb9eaae | cek | 224.47 | 201.96 | -10.03% [-10.37%, -9.69%] | 2059065 | 1951313 | faster | -12.56% |
| marlowe/semantics/65bc4b69b46d18fdff0fadbf00dd5ec2b3e03805fac9d5fb4ff2d3066e53fc7e | cek | 1359.57 | 1329.72 | -2.19% [-3.18%, -1.40%] | 10429227 | 10363723 | faster | -8.58% |
| marlowe/semantics/66af9e473d75e3f464971f6879cc0f2ef84bafcb38fbfa1dbc31ac2053628a38 | cek | 477.06 | 472.21 | -1.02% [-1.52%, -0.52%] | 4440231 | 4295551 | faster | -3.39% |
| marlowe/semantics/675d63836cad11b547d1b4cddd498f04c919d4342612accf40913f9ae9419fac | cek | 353.14 | 349.99 | -0.89% [-1.14%, -0.64%] | 3246817 | 3079241 | faster | -2.92% |
| marlowe/semantics/67ba5a9a0245ee3aff4f34852b9889b8c810fccd3dce2a23910bddd35c503b71 | cek | 3171.73 | 3183.08 | +0.34% [-0.88%, +1.97%] | 19440822 | 19379102 | inconclusive | -5.85% |
| marlowe/semantics/6d88f7294dd2b5ce02c3dc609bc7715bd508009738401d264bf9b3eb7c6f49c1 | cek | 164.55 | 148.96 | -9.48% [-9.79%, -9.16%] | 1544591 | 1462871 | faster | -11.61% |
| marlowe/semantics/70f65b21b77ddb451f3df9d9fb403ced3d10e1e953867cc4900cc25e5b9dec47 | cek | 276.85 | 259.01 | -5.96% [-11.99%, -2.59%] | 2411322 | 2297856 | faster | -9.53% |
| marlowe/semantics/71965c9ccae31f1ffc1d85aa20a356d4ed97a420954018d8301ec4f9783be0d7 | cek | 160.58 | 144.87 | -9.78% [-10.11%, -9.49%] | 1503766 | 1423326 | faster | -12.27% |
| marlowe/semantics/74c67f2f182b9a0a66c62b95d6fac5ace3f7e71ea3abfc52ffbe3ecb93436ea2 | cek | 269.44 | 267.42 | -0.75% [-0.96%, -0.52%] | 2531714 | 2404922 | faster | -2.81% |
| marlowe/semantics/7529b206a78becb793da74b78c04d9d33a2540a1abd79718e681228f4057403a | cek | 266.96 | 255.93 | -4.13% [-4.45%, -3.81%] | 2465769 | 2338881 | faster | -5.54% |
| marlowe/semantics/75a8bb183688bce447e00f435a144c835435e40a5defc6f3b9be68b70b4a3db6 | cek | 230.65 | 223.20 | -3.23% [-3.64%, -2.90%] | 2170053 | 2058191 | faster | -6.81% |
| marlowe/semantics/7a758e17486d1a30462c32a5d5309bd1e98322a9dcbe277c143ed3aede9d265f | cek | 179.21 | 168.23 | -6.13% [-6.51%, -5.77%] | 1584610 | 1506586 | faster | -9.14% |
| marlowe/semantics/7cbc5644b745f4ea635aca42cce5e4a4b9d2e61afdb3ac18128e1688c07071ba | cek | 167.21 | 148.84 | -10.98% [-11.40%, -10.70%] | 1589886 | 1511150 | faster | -14.08% |
| marlowe/semantics/82213dfdb6a812b40446438767c61a388d2c0cfd0cbf7fd4a372b0dc59fa17e1 | cek | 487.94 | 487.42 | -0.11% [-0.53%, +0.31%] | 4345480 | 4200296 | inconclusive | -2.32% |
| marlowe/semantics/8c7fdc3da6822b5112074380003524f50fb3a1ce6db4e501df1086773c6c0201 | cek | 377.80 | 362.55 | -4.03% [-4.27%, -3.83%] | 3485028 | 3305812 | faster | -5.81% |
| marlowe/semantics/8d9ae67656a2911ab15a8e5301c960c69aa2517055197aff6b60a87ff718d66c | cek | 122.67 | 108.49 | -11.56% [-12.01%, -10.96%] | 1120778 | 1061147 | faster | -12.26% |
| marlowe/semantics/96e1a2fa3ceb9a402f2a5841a0b645f87b4e8e75beb636692478ec39f74ee221 | cek | 105.24 | 93.77 | -10.90% [-11.22%, -10.56%] | 945818 | 893690 | faster | -12.70% |
| marlowe/semantics/9fabc4fc3440cdb776b28c9bb1dd49c9a5b1605fe1490aa3f4f64a3fa8881b25 | cek | 363.47 | 355.48 | -2.20% [-2.76%, -1.63%] | 3459849 | 3312011 | faster | -3.86% |
| marlowe/semantics/a85173a832db3ea944fafc406dfe3fa3235254897d6d1d0e21bc380147687bd5 | cek | 129.90 | 116.31 | -10.47% [-11.07%, -9.58%] | 1172187 | 1114091 | faster | -10.80% |
| marlowe/semantics/a9a853b6d083551f4ed2995551af287880ef42aee239a2d9bc5314d127cce592 | cek | 179.27 | 167.59 | -6.51% [-6.82%, -6.19%] | 1584607 | 1506583 | faster | +1.72% |
| marlowe/semantics/acb9c83c2b78dabef8674319ad69ba54912cd9997bdf2d8b2998c6bfeef3b122 | cek | 217.65 | 207.04 | -4.87% [-5.24%, -4.51%] | 2043781 | 1940340 | faster | -6.40% |
| marlowe/semantics/acce04815e8fd51be93322888250060da173eccf3df3a605bd6bc6a456cde871 | cek | 102.57 | 95.39 | -7.00% [-7.35%, -6.63%] | 1005361 | 959881 | faster | -9.64% |
| marlowe/semantics/ad6db94ed69b7161c7604568f44358e1cc11e81fea90e41afebd669e51bb60c8 | cek | 196.19 | 184.09 | -6.17% [-6.53%, -5.83%] | 1782749 | 1688932 | faster | -7.73% |
| marlowe/semantics/b21a4df3b0266ad3481a26d3e3d848aad2fcde89510b29cccce81971e38e0835 | cek | 478.78 | 442.07 | -7.55% [-10.57%, -5.86%] | 4367908 | 4155380 | faster | -8.39% |
| marlowe/semantics/b50170cea48ee84b80558c02b15c6df52faf884e504d2c410ad63ba46d8ca35c | cek | 254.40 | 236.44 | -7.06% [-7.19%, -6.93%] | 2411097 | 2283905 | faster | -8.66% |
| marlowe/semantics/bb5345bfbbc460af84e784b900ec270df1948bb1d1e29eacecd022eeb168b315 | cek | 331.49 | 324.98 | -1.96% [-2.31%, -1.59%] | 3020759 | 2863887 | faster | -2.84% |
| marlowe/semantics/c4bb185380df6e9b66fc1ee0564f09a8d1253a51a0c0c7890f2214df9ac19274 | cek | 245.76 | 238.65 | -2.89% [-3.29%, -2.50%] | 2325585 | 2205608 | faster | -8.85% |
| marlowe/semantics/c9efcb705ee057791f7c18a1de79c49f6e40ba143ce0579f1602fd780cabf153 | cek | 271.41 | 253.47 | -6.61% [-7.00%, -6.17%] | 2540608 | 2413520 | faster | -9.21% |
| marlowe/semantics/ccab11ce1a8774135d0e3c9e635631b68af9e276b5dabc66ff669d5650d0be1c | cek | 552.40 | 552.20 | -0.04% [-0.53%, +0.49%] | 5118881 | 5072702 | inconclusive | -4.92% |
| marlowe/semantics/cdb9d5c233b288a5a9dcfbd8d5c1831a0bb46eec7a26fa31b80ae69d44805efc | cek | 297.55 | 288.00 | -3.20% [-4.36%, -2.49%] | 2786306 | 2642888 | faster | -4.99% |
| marlowe/semantics/ced1ea04649e093a501e43f8568ac3e6b37cd3eccec8cac9c70a4857b88a5eb8 | cek | 279.96 | 263.93 | -5.73% [-6.13%, -5.35%] | 2666585 | 2530713 | faster | -7.73% |
| marlowe/semantics/cf542b7df466b228ca2197c2aaa89238a8122f3330fe5b77b3222f570395d9f5 | cek | 167.80 | 155.05 | -7.60% [-7.91%, -7.25%] | 1566695 | 1484495 | faster | -8.62% |
| marlowe/semantics/d1ab832dfab25688f8845bec9387e46ee3f00ba5822197ade7dd540489ec5e95 | cek | 20195.73 | 20299.70 | +0.52% [-0.51%, +1.51%] | 102685243 | 102642619 | inconclusive | +3.59% |
| marlowe/semantics/d1c03759810747b7cab38c4296593b38567e11195d161b5bb0a2b58f89b2c65a | cek | 338.23 | 327.87 | -3.07% [-3.29%, -2.79%] | 3208142 | 3041286 | faster | -4.17% |
| marlowe/semantics/d64607eb8a1448595081547ea8780886fcbd9e06036460eea3705c88ea867e33 | cek | 104.44 | 93.89 | -10.10% [-10.45%, -9.72%] | 939969 | 888041 | faster | -10.05% |
| marlowe/semantics/dc241ac6ad1e04fb056d555d6a4f2d08a45d054c6f7f34355fcfeefebef479f3 | cek | 159.12 | 146.72 | -7.80% [-8.10%, -7.50%] | 1465940 | 1387484 | faster | -9.04% |
| marlowe/semantics/dd11ae574eaeab0e9925319768989313a93913fdc347c704ddaa27042757d990 | cek | 252.35 | 234.92 | -6.91% [-7.26%, -6.52%] | 2391119 | 2264023 | faster | -9.87% |
| marlowe/semantics/e26c1cddba16e05fd10c34cbdb16ea6acdbac7c8323256c31c90c520ee6a1080 | cek | 133.57 | 118.87 | -10.94% [-13.30%, -9.49%] | 1205484 | 1147220 | faster | -10.16% |
| marlowe/semantics/e34b48f80d49360e88c612f4016f7d68cb5678dd8cd5ddb981375a028b3a40a5 | cek | 131.32 | 121.05 | -7.82% [-8.13%, -7.54%] | 1221067 | 1157171 | faster | -8.95% |
| marlowe/semantics/e3afd22d01ff12f381cf915fd32358634e6c413f979f2492cf3339319d8cc079 | cek | 104.81 | 93.52 | -10.78% [-11.26%, -10.31%] | 945818 | 893690 | faster | -12.19% |
| marlowe/semantics/e9234d2671760874f3f660aae5d3416d18ce6dfd7af4231bdd41b9ec268bc7e1 | cek | 431.83 | 429.00 | -0.65% [-1.07%, -0.29%] | 3865016 | 3780320 | faster | -0.43% |
| marlowe/semantics/eb4a605ed3a64961e9e66ad9631c2813dadf7131740212762ae4483ec749fe1d | cek | 104.57 | 93.74 | -10.36% [-10.67%, -10.07%] | 939969 | 888041 | faster | -10.53% |
| marlowe/semantics/ecb5e8308b57724e0f8533921693f111eba942123cf8660aac2b5bac21ec28f0 | cek | 230.71 | 215.78 | -6.47% [-6.90%, -5.97%] | 2055803 | 1956620 | faster | -7.91% |
| marlowe/semantics/f2a8fd2014922f0d8e01541205d47e9bb2d4e54333bdd408cbe7c47c55e73ae4 | cek | 276.68 | 264.18 | -4.52% [-4.88%, -4.06%] | 2516608 | 2427032 | faster | -7.16% |
| marlowe/semantics/f339f59bdf92495ed2b14e2e4d3705972b4dda59aa929cffe0f1ff5355db8d79 | cek | 2656.35 | 2717.64 | +2.31% [+1.48%, +3.18%] | 22316034 | 22271426 | slower | +2.42% |
| marlowe/semantics/ffdd68a33afd86f8844c9f5e45b2bda5b035aa02274161b23d57709c0f8b8de6 | cek | 330.12 | 320.34 | -2.72% [-7.06%, -0.19%] | 2975172 | 2826516 | faster | -2.44% |
| nofib/clausify/formula1 | cek | 1081.03 | 983.85 | -8.99% [-9.19%, -8.79%] | 13623555 | 12130304 | faster | -7.98% |
| nofib/clausify/formula2 | cek | 1445.93 | 1326.49 | -8.26% [-8.59%, -7.97%] | 17829638 | 15881358 | faster | -6.59% |
| nofib/clausify/formula3 | cek | 3949.61 | 3611.61 | -8.56% [-8.76%, -8.37%] | 48864148 | 43501844 | faster | -6.84% |
| nofib/clausify/formula4 | cek | 8139.74 | 7543.21 | -7.33% [-7.84%, -6.85%] | 99725338 | 89149498 | faster | -5.66% |
| nofib/clausify/formula5 | cek | 19277.38 | 17672.47 | -8.33% [-8.92%, -7.48%] | 238448321 | 212072406 | faster | -7.74% |
| nofib/knights/4x4 | cek | 6097.48 | 5802.23 | -4.84% [-5.12%, -4.54%] | 63311593 | 59000419 | faster | -4.80% |
| nofib/knights/6x6 | cek | 15918.62 | 14916.15 | -6.30% [-6.49%, -6.10%] | 187686663 | 173095650 | faster | -4.74% |
| nofib/knights/8x8 | cek | 28102.16 | 26255.58 | -6.57% [-6.92%, -6.18%] | 339749691 | 312527459 | faster | -5.23% |
| nofib/primetest/05digits | cek | 2441.71 | 2504.60 | +2.57% [+1.79%, +3.48%] | 22000263 | 21305406 | slower | +0.19% |
| nofib/primetest/10digits | cek | 5128.78 | 5164.28 | +0.69% [-0.01%, +1.49%] | 44756410 | 43406112 | inconclusive | -3.12% |
| nofib/primetest/30digits | cek | 15412.78 | 15605.11 | +1.25% [+0.76%, +1.69%] | 127994266 | 124376246 | slower | -2.63% |
| nofib/primetest/50digits | cek | 25870.38 | 26038.64 | +0.69% [-0.40%, +1.53%] | 205533677 | 199827501 | inconclusive | -2.24% |
| nofib/queens4x4/bjbt1 | cek | 2310.89 | 2211.16 | -4.32% [-4.55%, -4.06%] | 23118258 | 21352578 | faster | -3.32% |
| nofib/queens4x4/bjbt2 | cek | 2154.39 | 2071.10 | -3.87% [-4.42%, -3.02%] | 21533775 | 19925911 | faster | -4.13% |
| nofib/queens4x4/bm | cek | 2489.35 | 2383.29 | -4.26% [-4.79%, -3.76%] | 24465983 | 22568914 | faster | -4.22% |
| nofib/queens4x4/bt | cek | 1888.28 | 1808.39 | -4.23% [-4.83%, -3.64%] | 18775604 | 17382786 | faster | -4.36% |
| nofib/queens4x4/fc | cek | 4797.84 | 4570.72 | -4.73% [-5.13%, -4.34%] | 52077089 | 47975881 | faster | -4.38% |
| nofib/queens5x5/bjbt1 | cek | 29672.48 | 28709.15 | -3.25% [-3.54%, -2.99%] | 300915973 | 279081541 | faster | -4.03% |
| nofib/queens5x5/bjbt2 | cek | 29039.34 | 27832.73 | -4.10% [-5.98%, -2.92%] | 291195194 | 270327906 | faster | -4.53% |
| nofib/queens5x5/bm | cek | 27700.14 | 26961.91 | -2.71% [-3.81%, -0.75%] | 276285901 | 254711605 | faster | -3.18% |
| nofib/queens5x5/bt | cek | 25148.89 | 24367.68 | -3.11% [-3.36%, -2.88%] | 256433683 | 238388936 | faster | -3.57% |
| nofib/queens5x5/fc | cek | 59661.72 | 56553.05 | -5.21% [-5.73%, -4.72%] | 675782115 | 623283323 | faster | -1.67% |
| validation/auction_1-1 | cek | 86.29 | 83.36 | -3.39% [-4.35%, -2.52%] | 775944 | 737312 | faster | +5.23% |
| validation/auction_1-1 | full | 267.29 | 261.76 | -2.07% [-2.72%, -1.48%] | 1990383 | 1951751 | faster | -3.54% |
| validation/auction_1-2 | cek | 293.31 | 281.89 | -3.89% [-4.14%, -3.60%] | 2748707 | 2573635 | faster | -1.52% |
| validation/auction_1-2 | full | 898.98 | 882.92 | -1.79% [-2.27%, -1.23%] | 5821592 | 5646520 | faster | -2.64% |
| validation/auction_1-3 | cek | 285.34 | 279.79 | -1.95% [-2.35%, -1.56%] | 2761529 | 2584961 | faster | +0.16% |
| validation/auction_1-3 | full | 879.83 | 885.01 | +0.59% [-0.04%, +1.23%] | 5834452 | 5657884 | inconclusive | -1.46% |
| validation/auction_1-4 | cek | 113.45 | 108.58 | -4.30% [-4.78%, -3.90%] | 998866 | 951018 | faster | +2.68% |
| validation/auction_1-4 | full | 295.04 | 286.15 | -3.01% [-3.48%, -2.53%] | 2213306 | 2165458 | faster | -14.91% |
| validation/auction_2-1 | cek | 85.62 | 84.87 | -0.97% [-2.91%, +2.31%] | 775945 | 737313 | inconclusive | +4.29% |
| validation/auction_2-1 | full | 266.79 | 262.47 | -1.62% [-2.54%, -0.69%] | 1990384 | 1951752 | faster | -15.15% |
| validation/auction_2-2 | cek | 292.71 | 281.14 | -3.95% [-4.41%, -3.54%] | 2748709 | 2573637 | faster | -2.75% |
| validation/auction_2-2 | full | 902.42 | 884.76 | -1.96% [-2.45%, -1.45%] | 5821608 | 5646527 | faster | -14.07% |
| validation/auction_2-3 | cek | 384.50 | 361.95 | -5.87% [-6.16%, -5.56%] | 3635760 | 3404032 | faster | -3.64% |
| validation/auction_2-3 | full | 1032.46 | 1006.47 | -2.52% [-2.96%, -2.00%] | 6708648 | 6476921 | faster | -16.09% |
| validation/auction_2-4 | cek | 285.33 | 280.19 | -1.80% [-2.13%, -1.47%] | 2761533 | 2584965 | faster | +0.62% |
| validation/auction_2-4 | full | 878.06 | 880.51 | +0.28% [-0.15%, +0.72%] | 5834452 | 5657884 | inconclusive | -0.65% |
| validation/auction_2-5 | cek | 113.90 | 108.73 | -4.53% [-5.62%, -3.78%] | 998867 | 951019 | faster | +3.80% |
| validation/auction_2-5 | full | 296.16 | 287.06 | -3.07% [-4.21%, -1.75%] | 2213305 | 2165458 | faster | -4.41% |
| validation/coop-1 | cek | 120.35 | 121.26 | +0.85% [-2.14%, +2.73%] | 1113690 | 1076658 | inconclusive | +6.75% |
| validation/coop-1 | full | 214.33 | 219.79 | +2.53% [+1.72%, +3.71%] | 1739915 | 1702883 | slower | +3.15% |
| validation/coop-2 | cek | 377.07 | 389.71 | +3.31% [+2.29%, +5.01%] | 3384352 | 3233536 | slower | +9.40% |
| validation/coop-2 | full | 664.54 | 663.11 | -0.22% [-0.43%, +0.00%] | 4749617 | 4598802 | inconclusive | -12.25% |
| validation/coop-3 | cek | 1069.11 | 1022.36 | -4.37% [-4.70%, -4.04%] | 11384583 | 10565727 | faster | -0.96% |
| validation/coop-3 | full | 1416.42 | 1380.89 | -2.51% [-2.66%, -2.35%] | 12747922 | 11929066 | faster | -9.24% |
| validation/coop-4 | cek | 481.18 | 451.69 | -6.13% [-6.46%, -5.80%] | 4167971 | 3937793 | faster | -1.62% |
| validation/coop-4 | full | 819.69 | 800.24 | -2.37% [-2.63%, -2.12%] | 5740709 | 5510533 | faster | -2.93% |
| validation/coop-5 | cek | 204.90 | 197.39 | -3.66% [-4.02%, -3.36%] | 1836387 | 1752475 | faster | +1.27% |
| validation/coop-5 | full | 492.26 | 482.17 | -2.05% [-2.42%, -1.72%] | 3408693 | 3324781 | faster | -1.25% |
| validation/coop-6 | cek | 351.43 | 358.06 | +1.89% [+1.54%, +2.22%] | 3187477 | 3048413 | slower | +8.72% |
| validation/coop-6 | full | 487.34 | 492.16 | +0.99% [+0.57%, +1.39%] | 3907164 | 3768100 | slower | +2.55% |
| validation/coop-7 | cek | 166.19 | 171.73 | +3.33% [+2.93%, +3.67%] | 1552355 | 1502227 | slower | +3.86% |
| validation/coop-7 | full | 281.97 | 291.04 | +3.21% [+2.88%, +3.54%] | 2270098 | 2219970 | slower | +5.46% |
| validation/crowdfunding-success-1 | cek | 110.16 | 97.47 | -10.86% [-17.40%, -7.19%] | 896409 | 850209 | faster | +0.77% |
| validation/crowdfunding-success-1 | full | 322.91 | 313.09 | -3.04% [-3.76%, -2.27%] | 2395968 | 2349766 | faster | -3.01% |
| validation/crowdfunding-success-2 | cek | 105.01 | 97.20 | -7.43% [-8.05%, -6.84%] | 896411 | 850211 | faster | +1.19% |
| validation/crowdfunding-success-2 | full | 321.96 | 312.29 | -3.00% [-3.53%, -2.46%] | 2395966 | 2349766 | faster | -4.41% |
| validation/crowdfunding-success-3 | cek | 105.48 | 104.43 | -2.47% [-7.18%, +7.18%] | 896408 | 850208 | inconclusive | +2.53% |
| validation/crowdfunding-success-3 | full | 321.58 | 310.25 | -3.52% [-4.02%, -2.98%] | 2395966 | 2349768 | faster | -4.29% |
| validation/currency-1 | cek | 115.61 | 109.75 | -5.07% [-5.68%, -4.65%] | 1122722 | 1053409 | faster | -3.56% |
| validation/currency-1 | full | 340.15 | 334.96 | -1.53% [-2.16%, -0.96%] | 2584473 | 2515161 | faster | -4.49% |
| validation/escrow-redeem_1-1 | cek | 168.05 | 153.24 | -8.81% [-9.07%, -8.53%] | 1515361 | 1425489 | faster | -4.81% |
| validation/escrow-redeem_1-1 | full | 473.79 | 465.91 | -1.66% [-2.61%, -0.68%] | 3456111 | 3366239 | faster | -2.85% |
| validation/escrow-redeem_1-2 | cek | 167.70 | 153.17 | -8.66% [-9.23%, -7.89%] | 1515357 | 1425485 | faster | +0.32% |
| validation/escrow-redeem_1-2 | full | 475.56 | 467.06 | -1.79% [-2.50%, -0.97%] | 3456103 | 3366232 | faster | -3.76% |
| validation/escrow-redeem_2-1 | cek | 191.62 | 178.09 | -7.07% [-7.91%, -5.89%] | 1770240 | 1664920 | faster | -3.36% |
| validation/escrow-redeem_2-1 | full | 509.11 | 501.07 | -1.58% [-2.42%, -0.67%] | 3710999 | 3605679 | faster | -4.05% |
| validation/escrow-redeem_2-2 | cek | 192.75 | 178.25 | -7.53% [-7.85%, -7.23%] | 1770241 | 1664921 | faster | -3.42% |
| validation/escrow-redeem_2-2 | full | 508.40 | 498.53 | -1.94% [-2.57%, -1.38%] | 3710996 | 3605676 | faster | -4.89% |
| validation/escrow-redeem_2-3 | cek | 192.40 | 177.54 | -7.72% [-8.51%, -7.01%] | 1770244 | 1664924 | faster | -4.21% |
| validation/escrow-redeem_2-3 | full | 510.32 | 500.30 | -1.96% [-2.51%, -1.43%] | 3710993 | 3605673 | faster | -4.80% |
| validation/escrow-refund-1 | cek | 76.19 | 71.14 | -6.63% [-7.25%, -6.03%] | 663047 | 625655 | faster | +0.36% |
| validation/escrow-refund-1 | full | 363.84 | 360.14 | -1.02% [-1.77%, -0.27%] | 2603796 | 2566404 | faster | -4.15% |
| validation/future-increase-margin-1 | cek | 115.44 | 109.43 | -5.22% [-5.88%, -4.33%] | 1122803 | 1053490 | faster | -3.67% |
| validation/future-increase-margin-1 | full | 340.59 | 335.90 | -1.38% [-2.15%, -0.52%] | 2584423 | 2515111 | faster | -5.15% |
| validation/future-increase-margin-2 | cek | 256.19 | 232.60 | -9.20% [-9.77%, -8.74%] | 2369206 | 2226015 | faster | -2.09% |
| validation/future-increase-margin-2 | full | 590.74 | 618.41 | +4.68% [+3.91%, +5.39%] | 4325341 | 4182153 | slower | +4.54% |
| validation/future-increase-margin-3 | cek | 255.73 | 234.08 | -8.47% [-8.92%, -7.87%] | 2369207 | 2226014 | faster | -2.80% |
| validation/future-increase-margin-3 | full | 591.26 | 615.88 | +4.16% [+3.74%, +4.56%] | 4325397 | 4182204 | slower | +3.57% |
| validation/future-increase-margin-4 | cek | 226.97 | 205.70 | -9.37% [-9.63%, -9.14%] | 2062556 | 1930516 | faster | -3.35% |
| validation/future-increase-margin-4 | full | 921.21 | 908.07 | -1.43% [-1.94%, -0.98%] | 5788945 | 5656905 | faster | -3.37% |
| validation/future-increase-margin-5 | cek | 390.60 | 378.38 | -3.12% [-4.16%, -2.29%] | 3225207 | 3013357 | faster | +1.37% |
| validation/future-increase-margin-5 | full | 1119.01 | 1128.70 | +0.87% [+0.31%, +1.37%] | 6951655 | 6739813 | slower | -0.44% |
| validation/future-pay-out-1 | cek | 115.46 | 108.92 | -5.66% [-5.96%, -5.33%] | 1122802 | 1053490 | faster | -4.12% |
| validation/future-pay-out-1 | full | 338.80 | 332.61 | -1.83% [-2.72%, -1.04%] | 2584422 | 2515110 | faster | -4.10% |
| validation/future-pay-out-2 | cek | 255.52 | 233.19 | -8.74% [-9.25%, -8.05%] | 2369206 | 2226011 | faster | -0.69% |
| validation/future-pay-out-2 | full | 591.18 | 617.97 | +4.53% [+3.80%, +5.24%] | 4325335 | 4182153 | slower | +5.77% |
| validation/future-pay-out-3 | cek | 255.32 | 233.10 | -8.70% [-9.15%, -8.27%] | 2369211 | 2226019 | faster | -2.61% |
| validation/future-pay-out-3 | full | 592.60 | 616.80 | +4.08% [+3.40%, +4.69%] | 4325342 | 4182150 | slower | -11.01% |
| validation/future-pay-out-4 | cek | 389.80 | 366.37 | -6.03% [-6.73%, -5.00%] | 3218297 | 3006641 | faster | -4.41% |
| validation/future-pay-out-4 | full | 1138.45 | 1137.74 | -0.06% [-0.36%, +0.20%] | 6944745 | 6733083 | inconclusive | -11.26% |
| validation/future-settle-early-1 | cek | 115.55 | 108.89 | -5.77% [-6.06%, -5.52%] | 1122802 | 1053490 | faster | -4.50% |
| validation/future-settle-early-1 | full | 341.12 | 334.35 | -1.98% [-2.43%, -1.46%] | 2584428 | 2515116 | faster | -9.93% |
| validation/future-settle-early-2 | cek | 255.53 | 233.19 | -8.75% [-9.25%, -7.98%] | 2369207 | 2226014 | faster | +0.65% |
| validation/future-settle-early-2 | full | 589.10 | 620.14 | +5.27% [+4.45%, +6.02%] | 4325348 | 4182152 | slower | +3.60% |
| validation/future-settle-early-3 | cek | 255.63 | 232.46 | -9.06% [-9.42%, -8.68%] | 2369206 | 2226015 | faster | -1.67% |
| validation/future-settle-early-3 | full | 591.81 | 618.61 | +4.53% [+3.92%, +5.12%] | 4325337 | 4182149 | slower | +3.85% |
| validation/future-settle-early-4 | cek | 292.43 | 274.09 | -6.27% [-6.46%, -6.09%] | 2340681 | 2189577 | faster | -3.52% |
| validation/future-settle-early-4 | full | 1032.66 | 1009.76 | -2.16% [-4.49%, -0.69%] | 6067146 | 5916042 | faster | -0.58% |
| validation/game-sm-success_1-1 | cek | 186.11 | 169.26 | -9.05% [-9.27%, -8.85%] | 1627280 | 1529336 | faster | -4.62% |
| validation/game-sm-success_1-1 | full | 709.76 | 700.53 | -1.30% [-1.96%, -0.71%] | 4627491 | 4529547 | faster | -2.16% |
| validation/game-sm-success_1-2 | cek | 97.18 | 94.82 | -2.43% [-2.81%, -2.00%] | 868288 | 826232 | faster | +4.72% |
| validation/game-sm-success_1-2 | full | 247.47 | 241.63 | -2.36% [-3.13%, -1.54%] | 1926062 | 1884006 | faster | -1.54% |
| validation/game-sm-success_1-3 | cek | 287.49 | 283.42 | -1.42% [-1.81%, -0.95%] | 2746762 | 2572882 | faster | +1.60% |
| validation/game-sm-success_1-3 | full | 868.00 | 867.58 | -0.05% [-0.57%, +0.51%] | 5747033 | 5573149 | inconclusive | -4.62% |
| validation/game-sm-success_1-4 | cek | 111.33 | 111.20 | -0.12% [-1.00%, +0.55%] | 1008833 | 960641 | inconclusive | +7.13% |
| validation/game-sm-success_1-4 | full | 268.86 | 260.92 | -2.96% [-3.61%, -2.30%] | 2066608 | 2018416 | faster | -4.61% |
| validation/game-sm-success_2-1 | cek | 186.10 | 170.73 | -8.29% [-9.11%, -6.88%] | 1627282 | 1529339 | faster | -4.72% |
| validation/game-sm-success_2-1 | full | 707.19 | 697.65 | -1.35% [-1.94%, -0.78%] | 4627496 | 4529552 | faster | -2.89% |
| validation/game-sm-success_2-2 | cek | 97.44 | 95.26 | -2.24% [-2.71%, -1.77%] | 868288 | 826232 | faster | +4.12% |
| validation/game-sm-success_2-2 | full | 246.78 | 240.76 | -2.44% [-3.34%, -1.65%] | 1926062 | 1884006 | faster | -2.89% |
| validation/game-sm-success_2-3 | cek | 287.80 | 283.22 | -1.59% [-1.90%, -1.31%] | 2746768 | 2572888 | faster | +1.60% |
| validation/game-sm-success_2-3 | full | 868.88 | 871.49 | +0.30% [-0.30%, +0.88%] | 5746978 | 5573093 | inconclusive | -0.44% |
| validation/game-sm-success_2-4 | cek | 110.65 | 111.25 | +0.54% [-0.08%, +1.20%] | 1008833 | 960641 | inconclusive | +6.90% |
| validation/game-sm-success_2-4 | full | 269.88 | 258.30 | -4.27% [-5.40%, -3.42%] | 2066608 | 2018416 | faster | -4.94% |
| validation/game-sm-success_2-5 | cek | 290.37 | 282.72 | -2.62% [-3.93%, -1.65%] | 2746763 | 2572883 | faster | +1.81% |
| validation/game-sm-success_2-5 | full | 869.33 | 870.38 | +0.12% [-0.48%, +0.76%] | 5746979 | 5573099 | inconclusive | +0.56% |
| validation/game-sm-success_2-6 | cek | 110.84 | 111.20 | +0.33% [-0.09%, +0.70%] | 1008833 | 960641 | inconclusive | +6.63% |
| validation/game-sm-success_2-6 | full | 267.89 | 257.84 | -3.75% [-4.20%, -3.31%] | 2066608 | 2018416 | faster | -3.01% |
| validation/guardrail-sorted-large | cek | 216.11 | 211.07 | -2.33% [-2.61%, -2.09%] | 2152091 | 2020275 | faster | +1.85% |
| validation/guardrail-sorted-large | full | 324.96 | 312.09 | -3.96% [-4.24%, -3.69%] | 2813204 | 2681388 | faster | -2.26% |
| validation/guardrail-sorted-small | cek | 35.02 | 33.86 | -3.32% [-4.27%, -2.06%] | 351507 | 341299 | faster | +1.04% |
| validation/guardrail-sorted-small | full | 127.51 | 123.18 | -3.39% [-3.83%, -2.95%] | 1020107 | 1009899 | faster | -12.33% |
| validation/guardrail-unsorted-large | cek | 303.74 | 293.84 | -3.26% [-3.70%, -2.79%] | 3085857 | 2885337 | faster | +0.67% |
| validation/guardrail-unsorted-large | full | 411.51 | 400.25 | -2.74% [-3.07%, -2.39%] | 3741988 | 3541468 | faster | -12.50% |
| validation/guardrail-unsorted-small | cek | 34.16 | 32.56 | -4.64% [-6.08%, -3.63%] | 342963 | 333379 | faster | +1.23% |
| validation/guardrail-unsorted-small | full | 125.22 | 123.64 | -1.30% [-2.90%, +0.65%] | 1006579 | 996995 | inconclusive | -3.87% |
| validation/multisig-sm-01 | cek | 186.48 | 167.47 | -10.20% [-10.62%, -9.71%] | 1672432 | 1567888 | faster | -8.14% |
| validation/multisig-sm-01 | full | 763.80 | 765.08 | +0.17% [-0.41%, +0.73%] | 4949023 | 4844479 | inconclusive | -2.17% |
| validation/multisig-sm-02 | cek | 182.51 | 163.45 | -10.44% [-10.82%, -10.09%] | 1623575 | 1523358 | faster | -7.05% |
| validation/multisig-sm-02 | full | 758.47 | 748.74 | -1.28% [-2.07%, -0.70%] | 4900164 | 4799948 | faster | -3.26% |
| validation/multisig-sm-03 | cek | 183.97 | 170.14 | -7.52% [-7.84%, -7.13%] | 1642992 | 1541927 | faster | -4.21% |
| validation/multisig-sm-03 | full | 758.40 | 754.37 | -0.53% [-1.13%, +0.02%] | 4919585 | 4818521 | inconclusive | -3.59% |
| validation/multisig-sm-04 | cek | 185.01 | 165.75 | -10.41% [-10.71%, -10.10%] | 1662271 | 1560358 | faster | -7.50% |
| validation/multisig-sm-04 | full | 766.50 | 762.33 | -0.55% [-1.03%, -0.15%] | 4938869 | 4836957 | faster | -3.25% |
| validation/multisig-sm-05 | cek | 256.18 | 242.07 | -5.45% [-7.66%, -4.11%] | 2384333 | 2232517 | faster | -2.17% |
| validation/multisig-sm-05 | full | 883.95 | 859.38 | -2.78% [-3.06%, -2.50%] | 5660972 | 5509155 | faster | -2.19% |
| validation/multisig-sm-06 | cek | 186.84 | 167.38 | -10.41% [-10.80%, -10.09%] | 1672433 | 1567889 | faster | -7.09% |
| validation/multisig-sm-06 | full | 767.72 | 765.70 | -0.26% [-1.02%, +0.46%] | 4949027 | 4844483 | inconclusive | -2.70% |
| validation/multisig-sm-07 | cek | 181.99 | 164.00 | -9.90% [-10.56%, -8.88%] | 1623574 | 1523359 | faster | -4.16% |
| validation/multisig-sm-07 | full | 756.29 | 751.95 | -0.57% [-1.23%, +0.14%] | 4900160 | 4799944 | inconclusive | -3.57% |
| validation/multisig-sm-08 | cek | 187.68 | 169.68 | -9.57% [-10.73%, -8.80%] | 1642994 | 1541932 | faster | -4.62% |
| validation/multisig-sm-08 | full | 759.66 | 753.52 | -0.81% [-1.29%, -0.29%] | 4919579 | 4818515 | faster | -3.02% |
| validation/multisig-sm-09 | cek | 185.83 | 165.48 | -10.95% [-11.38%, -10.59%] | 1662271 | 1560358 | faster | -8.69% |
| validation/multisig-sm-09 | full | 764.49 | 760.16 | -0.56% [-1.12%, -0.02%] | 4938857 | 4836945 | faster | -1.17% |
| validation/multisig-sm-10 | cek | 251.52 | 241.73 | -3.89% [-4.20%, -3.57%] | 2384239 | 2232423 | faster | -1.89% |
| validation/multisig-sm-10 | full | 877.64 | 858.64 | -2.16% [-2.49%, -1.87%] | 5660871 | 5509055 | faster | -3.31% |
| validation/ping-pong-1 | cek | 156.14 | 141.99 | -9.06% [-9.80%, -8.48%] | 1399533 | 1313693 | faster | -5.40% |
| validation/ping-pong-1 | full | 653.32 | 606.50 | -7.17% [-7.83%, -6.46%] | 4226644 | 4140804 | faster | -11.89% |
| validation/ping-pong-2 | cek | 155.52 | 141.94 | -8.73% [-9.37%, -8.23%] | 1399533 | 1313693 | faster | -4.74% |
| validation/ping-pong-2 | full | 656.39 | 606.78 | -7.56% [-8.39%, -6.66%] | 4226642 | 4140802 | faster | -14.05% |
| validation/ping-pong_2-1 | cek | 98.71 | 90.25 | -8.57% [-9.01%, -8.11%] | 855128 | 802848 | faster | -2.48% |
| validation/ping-pong_2-1 | full | 562.98 | 542.93 | -3.34% [-7.86%, -0.72%] | 3682247 | 3629967 | faster | -3.30% |
| validation/prism-1 | cek | 80.95 | 77.74 | -3.96% [-4.35%, -3.56%] | 726135 | 691031 | faster | +4.27% |
| validation/prism-1 | full | 225.63 | 219.08 | -2.90% [-3.49%, -2.19%] | 1752108 | 1717004 | faster | -1.82% |
| validation/prism-2 | cek | 193.66 | 182.68 | -5.67% [-5.95%, -5.39%] | 1747033 | 1643585 | faster | -1.72% |
| validation/prism-2 | full | 718.51 | 700.28 | -2.54% [-3.12%, -1.87%] | 4707478 | 4604030 | faster | -2.22% |
| validation/prism-3 | cek | 174.53 | 166.67 | -4.50% [-4.78%, -4.22%] | 1624409 | 1530520 | faster | -0.52% |
| validation/prism-3 | full | 407.66 | 396.77 | -2.67% [-3.38%, -1.95%] | 3099195 | 3005305 | faster | -6.23% |
| validation/pubkey-1 | cek | 69.42 | 65.47 | -5.69% [-5.90%, -5.48%] | 616238 | 585446 | faster | +1.90% |
| validation/pubkey-1 | full | 219.63 | 214.28 | -2.43% [-2.96%, -1.92%] | 1674227 | 1643435 | faster | -5.66% |
| validation/stablecoin_1-1 | cek | 463.56 | 453.23 | -2.23% [-2.48%, -1.97%] | 3214549 | 3038351 | faster | +2.24% |
| validation/stablecoin_1-1 | full | 1447.65 | 1437.98 | -0.67% [-1.10%, -0.25%] | 7769599 | 7593407 | faster | -2.41% |
| validation/stablecoin_1-2 | cek | 95.42 | 92.26 | -3.31% [-4.41%, -2.60%] | 848304 | 807088 | faster | +6.71% |
| validation/stablecoin_1-2 | full | 244.86 | 238.80 | -2.47% [-3.32%, -1.64%] | 1906077 | 1864861 | faster | -2.66% |
| validation/stablecoin_1-3 | cek | 518.51 | 513.37 | -1.00% [-1.66%, -0.21%] | 3793900 | 3591593 | faster | +1.20% |
| validation/stablecoin_1-3 | full | 1650.48 | 1519.11 | -7.96% [-8.32%, -7.60%] | 8348943 | 8146639 | faster | -11.59% |
| validation/stablecoin_1-4 | cek | 101.02 | 97.05 | -3.92% [-4.39%, -3.43%] | 901040 | 857616 | faster | +2.17% |
| validation/stablecoin_1-4 | full | 256.05 | 244.88 | -4.36% [-5.00%, -3.71%] | 1958814 | 1915390 | faster | -14.63% |
| validation/stablecoin_1-5 | cek | 661.53 | 661.00 | -0.08% [-0.28%, +0.13%] | 4989361 | 4742913 | inconclusive | +2.83% |
| validation/stablecoin_1-5 | full | 1749.40 | 1719.81 | -1.69% [-2.04%, -1.35%] | 9544417 | 9297969 | faster | -13.99% |
| validation/stablecoin_1-6 | cek | 124.79 | 122.41 | -1.90% [-2.48%, -1.34%] | 1112178 | 1059562 | faster | +5.27% |
| validation/stablecoin_1-6 | full | 277.67 | 279.79 | +0.76% [-0.09%, +1.65%] | 2169953 | 2117337 | inconclusive | +0.60% |
| validation/stablecoin_2-1 | cek | 464.25 | 453.27 | -2.36% [-2.57%, -2.14%] | 3214550 | 3038350 | faster | +3.34% |
| validation/stablecoin_2-1 | full | 1453.30 | 1436.06 | -1.19% [-1.62%, -0.78%] | 7769615 | 7593415 | faster | -2.33% |
| validation/stablecoin_2-2 | cek | 95.04 | 92.25 | -2.93% [-3.26%, -2.57%] | 848304 | 807088 | faster | +5.44% |
| validation/stablecoin_2-2 | full | 245.22 | 239.40 | -2.37% [-3.07%, -1.66%] | 1906077 | 1864861 | faster | -3.25% |
| validation/stablecoin_2-3 | cek | 519.85 | 512.80 | -1.36% [-1.75%, -0.98%] | 3793895 | 3591591 | faster | +0.47% |
| validation/stablecoin_2-3 | full | 1652.24 | 1524.66 | -7.72% [-8.18%, -7.18%] | 8348935 | 8146638 | faster | -14.87% |
| validation/stablecoin_2-4 | cek | 101.14 | 97.16 | -3.94% [-4.35%, -3.56%] | 901040 | 857616 | faster | +2.13% |
| validation/stablecoin_2-4 | full | 257.73 | 245.76 | -4.63% [-5.79%, -3.60%] | 1958814 | 1915390 | faster | -5.91% |
| validation/token-account-1 | cek | 89.05 | 83.42 | -6.34% [-7.46%, -4.67%] | 832720 | 782928 | faster | -2.53% |
| validation/token-account-1 | full | 305.07 | 295.52 | -3.13% [-4.15%, -2.18%] | 2289394 | 2239602 | faster | -5.24% |
| validation/token-account-2 | cek | 156.00 | 149.11 | -4.41% [-4.82%, -3.95%] | 1519711 | 1428239 | faster | +0.06% |
| validation/token-account-2 | full | 367.52 | 364.03 | -0.95% [-1.61%, -0.33%] | 2878033 | 2786561 | faster | +0.24% |
| validation/uniswap-1 | cek | 185.61 | 179.23 | -3.44% [-3.68%, -3.20%] | 1940257 | 1816977 | faster | -0.41% |
| validation/uniswap-1 | full | 435.50 | 422.18 | -3.06% [-3.56%, -2.58%] | 3413125 | 3289845 | faster | -6.04% |
| validation/uniswap-2 | cek | 105.18 | 98.28 | -6.56% [-7.07%, -6.11%] | 978361 | 923001 | faster | -3.32% |
| validation/uniswap-2 | full | 324.49 | 313.14 | -3.50% [-4.46%, -2.44%] | 2435014 | 2379654 | faster | -6.38% |
| validation/uniswap-3 | cek | 810.80 | 803.44 | -0.91% [-1.25%, -0.56%] | 7490150 | 7109342 | faster | +2.27% |
| validation/uniswap-3 | full | 1734.30 | 1727.89 | -0.37% [-0.62%, -0.10%] | 11296742 | 10915934 | faster | -1.19% |
| validation/uniswap-4 | cek | 164.53 | 159.93 | -2.79% [-3.23%, -2.36%] | 1450503 | 1383039 | faster | +4.22% |
| validation/uniswap-4 | full | 332.18 | 334.14 | +0.59% [-0.05%, +1.25%] | 2576742 | 2509278 | inconclusive | +0.30% |
| validation/uniswap-5 | cek | 540.58 | 529.60 | -2.03% [-2.37%, -1.64%] | 4875491 | 4634803 | faster | +0.58% |
| validation/uniswap-5 | full | 1366.86 | 1372.60 | +0.42% [-0.22%, +1.08%] | 8692173 | 8451485 | inconclusive | +2.88% |
| validation/uniswap-6 | cek | 151.88 | 153.23 | +0.89% [+0.07%, +2.03%] | 1397437 | 1332109 | slower | +6.04% |
| validation/uniswap-6 | full | 326.65 | 319.89 | -2.07% [-2.79%, -1.36%] | 2523677 | 2458349 | faster | +4.73% |
| validation/vesting-1 | cek | 164.23 | 148.32 | -9.69% [-10.07%, -9.20%] | 1517750 | 1421454 | faster | -5.71% |
| validation/vesting-1 | full | 485.19 | 479.03 | -1.26% [-2.10%, -0.62%] | 3507652 | 3411356 | faster | -3.75% |

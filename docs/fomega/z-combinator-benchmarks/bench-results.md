We compare a fixed point operator defined directly by recursion

```haskell
fix' :: ((a -> b) -> a -> b) -> a -> b
fix' f x = (f $! fix' f) $! x
```

to the `Z` combinator defined via type-level recursion (equations are taken from the PFPL book):

```haskell
newtype Self a = Self { unfold :: Self a -> a }

-- unroll (self {τ} (x.e)) ↦ [self {τ} (x.e) / x] e
unroll :: Self a -> a
unroll s = unfold s s

-- | This function is adapted from the PFPL book.
-- fix {τ} (x. e) = unroll (self {τ} (y. [unroll y / x] e))
bz1 :: ((a -> b) -> a -> b) -> a -> b
bz1 = \f -> unroll . Self $ \s -> f (\x -> unroll s $! x)

-- | This function is from this Wikipedia article: https://en.wikipedia.org/wiki/Fixed-point_combinator#Strict_functional_implementation
z1 :: ((a -> b) -> a -> b) -> a -> b
z1 = \f -> let a = \r -> f (\x -> unroll r $! x) in a (Self a)
```

We also have functions that are exactly like `bz1` and `z1`, but with strictness placed differently:

```
-- fix {τ} (x. e) = unroll (self {τ} (y. [unroll y / x] e))
bz2 :: ((a -> b) -> a -> b) -> a -> b
bz2 = \f -> unroll . Self $ \s x -> (f $! unroll s) $! x

z2 :: ((a -> b) -> a -> b) -> a -> b
z2 = \f -> let a = \r x -> (f $! unroll r) $! x in a (Self a)
```

<details><summary> Results </summary>

benchmarking countdownBy/fix'/100000
time                 22.89 ms   (21.36 ms .. 24.08 ms)

                     0.983 R²   (0.956 R² .. 0.997 R²)

mean                 23.11 ms   (22.41 ms .. 23.59 ms)

std dev              1.369 ms   (952.1 μs .. 1.983 ms)

variance introduced by outliers: 24% (moderately inflated)


benchmarking countdownBy/bz1/100000
time                 22.68 ms   (20.55 ms .. 24.76 ms)

                     0.954 R²   (0.907 R² .. 0.982 R²)

mean                 21.01 ms   (19.27 ms .. 22.22 ms)

std dev              3.320 ms   (2.488 ms .. 4.363 ms)

variance introduced by outliers: 68% (severely inflated)


benchmarking countdownBy/bz2/100000
time                 28.14 ms   (24.45 ms .. 31.24 ms)

                     0.962 R²   (0.913 R² .. 0.991 R²)

mean                 30.21 ms   (28.31 ms .. 31.31 ms)

std dev              3.052 ms   (2.504 ms .. 3.872 ms)

variance introduced by outliers: 40% (moderately inflated)


benchmarking countdownBy/z1/100000
time                 21.93 ms   (20.20 ms .. 23.56 ms)

                     0.960 R²   (0.912 R² .. 0.988 R²)

mean                 22.43 ms   (21.12 ms .. 23.19 ms)

std dev              2.439 ms   (1.668 ms .. 3.512 ms)

variance introduced by outliers: 48% (moderately inflated)


benchmarking countdownBy/z2/100000
time                 31.92 ms   (27.46 ms .. 35.33 ms)

                     0.955 R²   (0.908 R² .. 0.997 R²)

mean                 32.54 ms   (30.63 ms .. 33.63 ms)

std dev              3.192 ms   (2.046 ms .. 4.165 ms)

variance introduced by outliers: 40% (moderately inflated)


benchmarking countdownBy/fix'/1000000
time                 230.0 ms   (207.3 ms .. 258.1 ms)

                     0.996 R²   (0.988 R² .. 1.000 R²)

mean                 219.9 ms   (208.3 ms .. 226.9 ms)

std dev              10.94 ms   (5.177 ms .. 15.75 ms)

variance introduced by outliers: 14% (moderately inflated)


benchmarking countdownBy/bz1/1000000
time                 196.5 ms   (141.3 ms .. 247.3 ms)

                     0.959 R²   (0.871 R² .. 1.000 R²)

mean                 203.8 ms   (183.6 ms .. 225.0 ms)

std dev              27.85 ms   (15.34 ms .. 37.71 ms)

variance introduced by outliers: 32% (moderately inflated)


benchmarking countdownBy/bz2/1000000
time                 311.1 ms   (289.9 ms .. 330.9 ms)

                     0.996 R²   (0.982 R² .. 1.000 R²)

mean                 324.8 ms   (315.5 ms .. 340.8 ms)

std dev              15.33 ms   (2.691 ms .. 19.51 ms)

variance introduced by outliers: 16% (moderately inflated)


benchmarking countdownBy/z1/1000000
time                 231.2 ms   (217.7 ms .. 257.9 ms)

                     0.993 R²   (0.974 R² .. 1.000 R²)

mean                 225.9 ms   (217.8 ms .. 234.0 ms)

std dev              11.00 ms   (6.347 ms .. 14.36 ms)

variance introduced by outliers: 14% (moderately inflated)


benchmarking countdownBy/z2/1000000
time                 318.0 ms   (278.2 ms .. 354.6 ms)

                     0.983 R²   (0.922 R² .. 1.000 R²)

mean                 313.2 ms   (293.1 ms .. 330.1 ms)

std dev              22.57 ms   (18.11 ms .. 25.91 ms)

variance introduced by outliers: 18% (moderately inflated)


benchmarking countdownBy/fix'/10000000
time                 2.266 s    (2.172 s .. 2.494 s)

                     0.999 R²   (0.996 R² .. 1.000 R²)

mean                 2.302 s    (2.256 s .. 2.329 s)

std dev              41.14 ms   (0.0 s .. 45.61 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking countdownBy/bz1/10000000
time                 2.282 s    (2.139 s .. 2.384 s)

                     1.000 R²   (0.999 R² .. 1.000 R²)

mean                 2.242 s    (2.215 s .. 2.256 s)

std dev              23.29 ms   (0.0 s .. 24.44 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking countdownBy/bz2/10000000
time                 3.335 s    (3.181 s .. 3.629 s)

                     0.999 R²   (0.998 R² .. 1.000 R²)

mean                 3.206 s    (3.164 s .. 3.246 s)

std dev              67.99 ms   (0.0 s .. 69.59 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking countdownBy/z1/10000000
time                 2.290 s    (2.233 s .. 2.380 s)

                     1.000 R²   (1.000 R² .. 1.000 R²)

mean                 2.242 s    (2.220 s .. 2.260 s)

std dev              26.50 ms   (0.0 s .. 29.82 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking countdownBy/z2/10000000
time                 3.204 s    (3.102 s .. 3.336 s)

                     1.000 R²   (1.000 R² .. 1.000 R²)

mean                 3.243 s    (3.209 s .. 3.265 s)

std dev              33.62 ms   (0.0 s .. 38.80 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking natSumUpToBy/fix'/100000
time                 23.01 ms   (21.63 ms .. 24.15 ms)

                     0.986 R²   (0.971 R² .. 0.995 R²)

mean                 22.09 ms   (20.77 ms .. 22.78 ms)

std dev              2.117 ms   (1.250 ms .. 3.268 ms)

variance introduced by outliers: 43% (moderately inflated)


benchmarking natSumUpToBy/bz1/100000
time                 22.99 ms   (21.95 ms .. 23.95 ms)

                     0.986 R²   (0.966 R² .. 0.995 R²)

mean                 21.36 ms   (20.06 ms .. 22.17 ms)

std dev              2.373 ms   (1.517 ms .. 3.782 ms)

variance introduced by outliers: 48% (moderately inflated)


benchmarking natSumUpToBy/bz2/100000
time                 28.63 ms   (26.95 ms .. 29.99 ms)

                     0.988 R²   (0.971 R² .. 0.997 R²)

mean                 28.04 ms   (26.90 ms .. 28.80 ms)

std dev              1.840 ms   (1.333 ms .. 2.477 ms)

variance introduced by outliers: 26% (moderately inflated)


benchmarking natSumUpToBy/z1/100000
time                 21.28 ms   (19.68 ms .. 23.02 ms)

                     0.969 R²   (0.940 R² .. 0.989 R²)

mean                 21.16 ms   (19.69 ms .. 21.93 ms)

std dev              2.486 ms   (1.674 ms .. 3.934 ms)

variance introduced by outliers: 55% (severely inflated)


benchmarking natSumUpToBy/z2/100000
time                 26.36 ms   (24.70 ms .. 28.41 ms)

                     0.979 R²   (0.968 R² .. 0.990 R²)

mean                 27.56 ms   (26.28 ms .. 28.55 ms)

std dev              2.402 ms   (1.901 ms .. 2.944 ms)

variance introduced by outliers: 37% (moderately inflated)


benchmarking natSumUpToBy/fix'/1000000
time                 220.8 ms   (158.2 ms .. 241.7 ms)

                     0.966 R²   (0.894 R² .. 1.000 R²)

mean                 222.1 ms   (204.8 ms .. 230.9 ms)

std dev              17.95 ms   (3.685 ms .. 24.12 ms)

variance introduced by outliers: 16% (moderately inflated)


benchmarking natSumUpToBy/bz1/1000000
time                 202.6 ms   (179.4 ms .. 223.8 ms)

                     0.989 R²   (0.946 R² .. 1.000 R²)

mean                 210.8 ms   (198.0 ms .. 222.5 ms)

std dev              15.15 ms   (9.143 ms .. 20.35 ms)

variance introduced by outliers: 15% (moderately inflated)


benchmarking natSumUpToBy/bz2/1000000
time                 281.0 ms   (219.8 ms .. 352.5 ms)

                     0.988 R²   (0.967 R² .. 1.000 R²)

mean                 269.8 ms   (253.6 ms .. 282.8 ms)

std dev              17.72 ms   (12.87 ms .. 20.93 ms)

variance introduced by outliers: 17% (moderately inflated)


benchmarking natSumUpToBy/z1/1000000
time                 215.4 ms   (179.6 ms .. 235.8 ms)

                     0.978 R²   (0.889 R² .. 1.000 R²)

mean                 213.8 ms   (196.0 ms .. 223.2 ms)

std dev              17.92 ms   (6.605 ms .. 25.63 ms)

variance introduced by outliers: 16% (moderately inflated)


benchmarking natSumUpToBy/z2/1000000
time                 280.3 ms   (258.1 ms .. 352.9 ms)

                     0.996 R²   (0.991 R² .. 1.000 R²)

mean                 276.1 ms   (269.9 ms .. 280.9 ms)

std dev              7.008 ms   (3.788 ms .. 9.847 ms)

variance introduced by outliers: 16% (moderately inflated)


benchmarking natSumUpToBy/fix'/10000000
time                 2.176 s    (1.902 s .. 2.357 s)

                     0.998 R²   (0.994 R² .. 1.000 R²)

mean                 2.240 s    (2.188 s .. 2.272 s)

std dev              48.14 ms   (0.0 s .. 55.08 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking natSumUpToBy/bz1/10000000
time                 2.208 s    (2.125 s .. 2.329 s)

                     1.000 R²   (0.999 R² .. 1.000 R²)

mean                 2.197 s    (2.169 s .. 2.215 s)

std dev              26.69 ms   (0.0 s .. 30.78 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking natSumUpToBy/bz2/10000000
time                 2.671 s    (2.590 s .. 2.840 s)

                     0.999 R²   (0.996 R² .. 1.000 R²)

mean                 2.757 s    (2.695 s .. 2.792 s)

std dev              55.21 ms   (0.0 s .. 60.19 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking natSumUpToBy/z1/10000000
time                 2.209 s    (2.098 s .. 2.370 s)

                     0.999 R²   (0.999 R² .. 1.000 R²)

mean                 2.160 s    (2.133 s .. 2.183 s)

std dev              36.64 ms   (0.0 s .. 39.79 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking natSumUpToBy/z2/10000000
time                 2.773 s    (2.589 s .. 2.903 s)

                     1.000 R²   (0.999 R² .. 1.000 R²)

mean                 2.799 s    (2.760 s .. 2.828 s)

std dev              43.20 ms   (0.0 s .. 49.33 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking leakingNatSumUpToBy/fix'/100000
time                 24.44 ms   (24.21 ms .. 24.68 ms)

                     1.000 R²   (0.999 R² .. 1.000 R²)

mean                 24.61 ms   (24.49 ms .. 24.72 ms)

std dev              272.1 μs   (211.5 μs .. 344.4 μs)


benchmarking leakingNatSumUpToBy/bz1/100000
time                 24.25 ms   (23.79 ms .. 24.64 ms)

                     0.998 R²   (0.995 R² .. 1.000 R²)

mean                 24.49 ms   (24.21 ms .. 25.34 ms)

std dev              1.000 ms   (498.0 μs .. 1.873 ms)

variance introduced by outliers: 15% (moderately inflated)


benchmarking leakingNatSumUpToBy/bz2/100000
time                 33.03 ms   (32.27 ms .. 33.70 ms)

                     0.998 R²   (0.996 R² .. 1.000 R²)

mean                 33.47 ms   (32.91 ms .. 34.35 ms)

std dev              1.378 ms   (884.6 μs .. 2.305 ms)

variance introduced by outliers: 12% (moderately inflated)


benchmarking leakingNatSumUpToBy/z1/100000
time                 25.37 ms   (24.82 ms .. 25.68 ms)

                     0.999 R²   (0.997 R² .. 1.000 R²)

mean                 25.82 ms   (25.58 ms .. 26.58 ms)

std dev              846.5 μs   (290.5 μs .. 1.360 ms)


benchmarking leakingNatSumUpToBy/z2/100000
time                 33.31 ms   (32.98 ms .. 33.71 ms)

                     0.999 R²   (0.998 R² .. 1.000 R²)

mean                 33.33 ms   (32.96 ms .. 33.85 ms)

std dev              922.9 μs   (552.9 μs .. 1.412 ms)


benchmarking leakingNatSumUpToBy/fix'/1000000
time                 293.7 ms   (288.7 ms .. 304.5 ms)

                     1.000 R²   (0.999 R² .. 1.000 R²)

mean                 297.8 ms   (295.9 ms .. 300.1 ms)

std dev              2.631 ms   (872.7 μs .. 3.559 ms)

variance introduced by outliers: 16% (moderately inflated)


benchmarking leakingNatSumUpToBy/bz1/1000000
time                 292.6 ms   (283.1 ms .. 303.3 ms)

                     1.000 R²   (0.999 R² .. 1.000 R²)

mean                 295.4 ms   (293.2 ms .. 297.0 ms)

std dev              2.222 ms   (889.8 μs .. 2.790 ms)

variance introduced by outliers: 16% (moderately inflated)


benchmarking leakingNatSumUpToBy/bz2/1000000
time                 396.0 ms   (370.0 ms .. 425.2 ms)

                     0.999 R²   (0.999 R² .. 1.000 R²)

mean                 395.4 ms   (392.5 ms .. 400.9 ms)

std dev              4.771 ms   (0.0 s .. 4.860 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking leakingNatSumUpToBy/z1/1000000
time                 315.0 ms   (308.9 ms .. 327.1 ms)

                     1.000 R²   (0.999 R² .. 1.000 R²)

mean                 314.4 ms   (310.8 ms .. 316.5 ms)

std dev              3.599 ms   (60.23 μs .. 5.027 ms)

variance introduced by outliers: 16% (moderately inflated)


benchmarking leakingNatSumUpToBy/z2/1000000
time                 392.8 ms   (385.4 ms .. 399.0 ms)

                     1.000 R²   (1.000 R² .. 1.000 R²)

mean                 394.0 ms   (393.0 ms .. 394.9 ms)

std dev              1.290 ms   (0.0 s .. 1.447 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking leakingNatSumUpToBy/fix'/10000000
time                 3.414 s    (3.342 s .. 3.445 s)

                     1.000 R²   (1.000 R² .. 1.000 R²)

mean                 3.462 s    (3.457 s .. 3.466 s)

std dev              6.328 ms   (0.0 s .. 7.218 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking leakingNatSumUpToBy/bz1/10000000
time                 3.315 s    (3.296 s .. 3.349 s)

                     1.000 R²   (1.000 R² .. 1.000 R²)

mean                 3.400 s    (3.369 s .. 3.424 s)

std dev              35.09 ms   (0.0 s .. 39.95 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking leakingNatSumUpToBy/bz2/10000000
time                 4.479 s    (4.270 s .. 4.636 s)

                     1.000 R²   (0.999 R² .. 1.000 R²)

mean                 4.516 s    (4.482 s .. 4.539 s)

std dev              35.49 ms   (0.0 s .. 40.78 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking leakingNatSumUpToBy/z1/10000000
time                 3.495 s    (3.065 s .. 3.846 s)

                     0.998 R²   (0.994 R² .. 1.000 R²)

mean                 3.609 s    (3.532 s .. 3.661 s)

std dev              77.76 ms   (0.0 s .. 89.78 ms)

variance introduced by outliers: 19% (moderately inflated)


benchmarking leakingNatSumUpToBy/z2/10000000
time                 4.505 s    (4.290 s .. 4.674 s)

                     1.000 R²   (NaN R² .. 1.000 R²)

mean                 4.565 s    (4.509 s .. 4.596 s)

std dev              49.45 ms   (0.0 s .. 54.40 ms)

variance introduced by outliers: 19% (moderately inflated)

</details>
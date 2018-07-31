# The `Z` combinator becnhmarks

## Preface

Here we explore the possibility of using type-level recursion in order to define a term-level recursion combinator in a strict setting. The standard `Y` combinator

```
Y f
  = (\r. f (r r)) (\r. f (r r))
  ↦ f ((\r. f (r r)) (\r. f (r r)))
  ~ f (Y f)
```

loops in such a setting, because in the last step `Y f` must be evaluated before its results is passed to `f` and this is an infinite recursion. The common way to mitigate this is via eta-expansion of `f`:

```
Z f
  = (\r. f (\x. r r x)) (\r. f (\x. r r x))
  ↦ f (\x. (\r. f (\x. r r x)) (\r. f (\x. r r x)) x)
  ~ f (\x. Z f x)
```

Since in a usual strict setting functions get evaluated only when they're applied to all necessary arguments, `\x. Z f x` does not reduces any further and gets passed to `f` as is. Hence infinite recursion is broken. The trade-off is that `Z` has more restrictive type than `Y`, it's

```
((a -> b) -> a -> b) -> a -> b
```

versus

```
(a -> a) -> a
```

due to the eta-expansion of `f`.

## Details

We compare a fixed point operator defined directly by recursion

```haskell
fix' :: ((a -> b) -> a -> b) -> a -> b
fix' f x = (f $! fix' f) $! x
```

to the `Z` combinator defined via type-level recursion (equations are taken from the PFPL book):

```haskell
newtype Fix f = Fix (f (Fix f))

newtype SelfF a r = SelfF
  { unSelfF :: r -> a
  }

type Self a = Fix (SelfF a)

pattern Self f = Fix (SelfF f)

unfold :: Self a -> Self a -> a
unfold (Self f) = f

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

```haskell
-- fix {τ} (x. e) = unroll (self {τ} (y. [unroll y / x] e))
bz2 :: ((a -> b) -> a -> b) -> a -> b
bz2 = \f -> unroll . Self $ \s x -> (f $! unroll s) $! x

z2 :: ((a -> b) -> a -> b) -> a -> b
z2 = \f -> let a = \r x -> (f $! unroll r) $! x in a (Self a)
```

In short, `bz1` and `z1` are mostly on par with `fix'`, but sometimes can be up to 20% slower or faster in no predictable way. `bz2` and `z2` are reliably slower than `fix'` by a factor of 1.2 - 1.5. Why the difference? No idea.

## Results

<details>
  <summary> Results </summary>
  <p>

```
benchmarking countdownBy/fix'/1000000
time                 235.7 ms   (186.6 ms .. 270.1 ms)
                     0.980 R²   (0.907 R² .. 1.000 R²)
mean                 237.7 ms   (222.1 ms .. 249.1 ms)
std dev              17.30 ms   (8.598 ms .. 21.42 ms)
variance introduced by outliers: 15% (moderately inflated)

benchmarking countdownBy/bz1/1000000
time                 244.2 ms   (229.5 ms .. 258.7 ms)
                     0.997 R²   (0.987 R² .. 1.000 R²)
mean                 241.6 ms   (234.0 ms .. 245.6 ms)
std dev              7.296 ms   (3.137 ms .. 9.153 ms)
variance introduced by outliers: 16% (moderately inflated)

benchmarking countdownBy/bz2/1000000
time                 358.9 ms   (277.4 ms .. 416.2 ms)
                     0.994 R²   (0.980 R² .. 1.000 R²)
mean                 349.0 ms   (332.8 ms .. 358.2 ms)
std dev              14.42 ms   (0.0 s .. 15.98 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking countdownBy/z1/1000000
time                 227.9 ms   (199.4 ms .. 247.2 ms)
                     0.994 R²   (0.981 R² .. 1.000 R²)
mean                 231.1 ms   (225.6 ms .. 243.0 ms)
std dev              9.433 ms   (2.201 ms .. 13.14 ms)
variance introduced by outliers: 14% (moderately inflated)

benchmarking countdownBy/z2/1000000
time                 350.1 ms   (295.6 ms .. 431.7 ms)
                     0.994 R²   (0.983 R² .. 1.000 R²)
mean                 330.4 ms   (307.2 ms .. 344.3 ms)
std dev              21.20 ms   (0.0 s .. 23.97 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking countdownBy/fix'/10000000
time                 2.284 s    (1.884 s .. 2.561 s)
                     0.997 R²   (0.989 R² .. 1.000 R²)
mean                 2.364 s    (2.295 s .. 2.410 s)
std dev              68.53 ms   (0.0 s .. 79.09 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking countdownBy/bz1/10000000
time                 2.397 s    (2.306 s .. 2.474 s)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 2.431 s    (2.408 s .. 2.448 s)
std dev              26.25 ms   (0.0 s .. 29.69 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking countdownBy/bz2/10000000
time                 3.429 s    (3.243 s .. 3.630 s)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 3.498 s    (3.439 s .. 3.534 s)
std dev              54.86 ms   (0.0 s .. 62.94 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking countdownBy/z1/10000000
time                 2.392 s    (2.255 s .. 2.493 s)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 2.379 s    (2.355 s .. 2.396 s)
std dev              25.30 ms   (0.0 s .. 29.10 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking countdownBy/z2/10000000
time                 3.296 s    (2.937 s .. 3.687 s)
                     0.998 R²   (0.994 R² .. 1.000 R²)
mean                 3.315 s    (3.259 s .. 3.363 s)
std dev              75.96 ms   (0.0 s .. 82.49 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking natSumUpToBy/fix'/100000
time                 24.52 ms   (23.51 ms .. 25.25 ms)
                     0.983 R²   (0.953 R² .. 1.000 R²)
mean                 24.34 ms   (22.95 ms .. 24.93 ms)
std dev              1.761 ms   (676.1 μs .. 3.141 ms)
variance introduced by outliers: 30% (moderately inflated)

benchmarking natSumUpToBy/bz1/100000
time                 23.58 ms   (18.86 ms .. 27.39 ms)
                     0.920 R²   (0.807 R² .. 0.985 R²)
mean                 22.93 ms   (21.27 ms .. 24.37 ms)
std dev              3.661 ms   (2.865 ms .. 4.659 ms)
variance introduced by outliers: 68% (severely inflated)

benchmarking natSumUpToBy/bz2/100000
time                 33.30 ms   (31.10 ms .. 35.16 ms)
                     0.985 R²   (0.969 R² .. 0.995 R²)
mean                 32.26 ms   (31.17 ms .. 33.31 ms)
std dev              2.469 ms   (1.904 ms .. 2.844 ms)
variance introduced by outliers: 28% (moderately inflated)

benchmarking natSumUpToBy/z1/100000
time                 25.89 ms   (23.47 ms .. 27.32 ms)
                     0.971 R²   (0.927 R² .. 1.000 R²)
mean                 25.14 ms   (23.68 ms .. 25.98 ms)
std dev              2.415 ms   (1.318 ms .. 3.398 ms)
variance introduced by outliers: 41% (moderately inflated)

benchmarking natSumUpToBy/z2/100000
time                 33.40 ms   (31.26 ms .. 34.86 ms)
                     0.983 R²   (0.939 R² .. 1.000 R²)
mean                 32.66 ms   (31.05 ms .. 33.40 ms)
std dev              2.254 ms   (1.438 ms .. 3.380 ms)
variance introduced by outliers: 24% (moderately inflated)

benchmarking natSumUpToBy/fix'/1000000
time                 251.4 ms   (216.5 ms .. 274.9 ms)
                     0.995 R²   (0.989 R² .. 1.000 R²)
mean                 246.7 ms   (238.2 ms .. 251.7 ms)
std dev              10.10 ms   (6.874 ms .. 11.70 ms)
variance introduced by outliers: 16% (moderately inflated)

benchmarking natSumUpToBy/bz1/1000000
time                 241.0 ms   (206.4 ms .. 271.1 ms)
                     0.993 R²   (0.991 R² .. 1.000 R²)
mean                 252.0 ms   (241.9 ms .. 256.8 ms)
std dev              9.570 ms   (1.816 ms .. 12.17 ms)
variance introduced by outliers: 16% (moderately inflated)

benchmarking natSumUpToBy/bz2/1000000
time                 316.4 ms   (285.0 ms .. 347.2 ms)
                     0.992 R²   (0.983 R² .. 1.000 R²)
mean                 330.0 ms   (316.0 ms .. 338.8 ms)
std dev              13.32 ms   (4.549 ms .. 17.50 ms)
variance introduced by outliers: 16% (moderately inflated)

benchmarking natSumUpToBy/z1/1000000
time                 244.1 ms   (177.6 ms .. 293.4 ms)
                     0.970 R²   (0.895 R² .. 1.000 R²)
mean                 238.8 ms   (202.0 ms .. 256.0 ms)
std dev              26.05 ms   (1.273 ms .. 32.61 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking natSumUpToBy/z2/1000000
time                 353.2 ms   (333.9 ms .. 367.6 ms)
                     0.997 R²   (0.985 R² .. 1.000 R²)
mean                 332.8 ms   (323.7 ms .. 337.5 ms)
std dev              9.073 ms   (5.864 μs .. 10.78 ms)
variance introduced by outliers: 16% (moderately inflated)

benchmarking natSumUpToBy/fix'/10000000
time                 2.416 s    (2.381 s .. 2.437 s)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 2.417 s    (2.413 s .. 2.423 s)
std dev              5.362 ms   (0.0 s .. 6.081 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking natSumUpToBy/bz1/10000000
time                 2.518 s    (2.445 s .. 2.591 s)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 2.494 s    (2.482 s .. 2.500 s)
std dev              10.06 ms   (0.0 s .. 10.93 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking natSumUpToBy/bz2/10000000
time                 3.359 s    (3.228 s .. 3.483 s)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 3.308 s    (3.282 s .. 3.325 s)
std dev              25.13 ms   (0.0 s .. 28.98 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking natSumUpToBy/z1/10000000
time                 2.480 s    (2.296 s .. 2.709 s)
                     0.999 R²   (0.997 R² .. 1.000 R²)
mean                 2.452 s    (2.401 s .. 2.486 s)
std dev              51.43 ms   (0.0 s .. 59.39 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking natSumUpToBy/z2/10000000
time                 3.331 s    (3.260 s .. 3.482 s)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 3.327 s    (3.309 s .. 3.341 s)
std dev              21.50 ms   (0.0 s .. 24.04 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking leakingNatSumUpToBy/fix'/100000
time                 24.01 ms   (23.21 ms .. 24.46 ms)
                     0.997 R²   (0.992 R² .. 1.000 R²)
mean                 24.71 ms   (24.34 ms .. 25.62 ms)
std dev              1.313 ms   (409.7 μs .. 2.412 ms)
variance introduced by outliers: 20% (moderately inflated)

benchmarking leakingNatSumUpToBy/bz1/100000
time                 26.05 ms   (25.46 ms .. 26.46 ms)
                     0.998 R²   (0.995 R² .. 1.000 R²)
mean                 26.32 ms   (26.03 ms .. 27.45 ms)
std dev              1.128 ms   (419.1 μs .. 2.200 ms)
variance introduced by outliers: 15% (moderately inflated)

benchmarking leakingNatSumUpToBy/bz2/100000
time                 34.04 ms   (33.12 ms .. 34.58 ms)
                     0.999 R²   (0.997 R² .. 1.000 R²)
mean                 34.81 ms   (34.45 ms .. 36.00 ms)
std dev              1.263 ms   (463.1 μs .. 2.127 ms)
variance introduced by outliers: 11% (moderately inflated)

benchmarking leakingNatSumUpToBy/z1/100000
time                 25.89 ms   (25.24 ms .. 26.36 ms)
                     0.998 R²   (0.995 R² .. 1.000 R²)
mean                 26.15 ms   (25.80 ms .. 27.06 ms)
std dev              1.257 ms   (271.6 μs .. 2.385 ms)
variance introduced by outliers: 15% (moderately inflated)

benchmarking leakingNatSumUpToBy/z2/100000
time                 33.88 ms   (32.92 ms .. 34.94 ms)
                     0.997 R²   (0.994 R² .. 0.999 R²)
mean                 34.87 ms   (34.38 ms .. 36.26 ms)
std dev              1.526 ms   (740.8 μs .. 2.570 ms)
variance introduced by outliers: 12% (moderately inflated)

benchmarking leakingNatSumUpToBy/fix'/1000000
time                 285.6 ms   (276.5 ms .. 294.1 ms)
                     0.999 R²   (0.995 R² .. 1.000 R²)
mean                 298.2 ms   (291.6 ms .. 306.7 ms)
std dev              9.391 ms   (809.2 μs .. 11.94 ms)
variance introduced by outliers: 16% (moderately inflated)

benchmarking leakingNatSumUpToBy/bz1/1000000
time                 303.3 ms   (295.2 ms .. 306.9 ms)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 312.1 ms   (308.3 ms .. 317.3 ms)
std dev              5.092 ms   (1.747 ms .. 6.796 ms)
variance introduced by outliers: 16% (moderately inflated)

benchmarking leakingNatSumUpToBy/bz2/1000000
time                 402.0 ms   (358.0 ms .. 443.1 ms)
                     0.998 R²   (0.994 R² .. 1.000 R²)
mean                 401.4 ms   (395.1 ms .. 406.7 ms)
std dev              8.567 ms   (0.0 s .. 9.245 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking leakingNatSumUpToBy/z1/1000000
time                 303.5 ms   (293.6 ms .. 319.9 ms)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 311.1 ms   (309.2 ms .. 313.9 ms)
std dev              2.706 ms   (677.1 μs .. 3.629 ms)
variance introduced by outliers: 16% (moderately inflated)

benchmarking leakingNatSumUpToBy/z2/1000000
time                 397.7 ms   (360.4 ms .. 428.4 ms)
                     0.999 R²   (0.996 R² .. 1.000 R²)
mean                 399.8 ms   (395.5 ms .. 403.7 ms)
std dev              6.467 ms   (642.1 μs .. 6.764 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking leakingNatSumUpToBy/fix'/10000000
time                 3.375 s    (3.000 s .. 3.651 s)
                     0.999 R²   (0.995 R² .. 1.000 R²)
mean                 3.444 s    (3.383 s .. 3.487 s)
std dev              63.88 ms   (0.0 s .. 73.63 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking leakingNatSumUpToBy/bz1/10000000
time                 3.591 s    (3.511 s .. 3.646 s)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 3.622 s    (3.604 s .. 3.633 s)
std dev              16.35 ms   (0.0 s .. 17.80 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking leakingNatSumUpToBy/bz2/10000000
time                 4.552 s    (4.339 s .. 4.850 s)
                     1.000 R²   (0.998 R² .. 1.000 R²)
mean                 4.588 s    (4.543 s .. 4.622 s)
std dev              52.15 ms   (0.0 s .. 59.02 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking leakingNatSumUpToBy/z1/10000000
time                 3.622 s    (3.525 s .. 3.749 s)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 3.626 s    (3.610 s .. 3.640 s)
std dev              23.71 ms   (0.0 s .. 24.70 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking leakingNatSumUpToBy/z2/10000000
time                 4.521 s    (4.450 s .. 4.577 s)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 4.625 s    (4.586 s .. 4.649 s)
std dev              36.54 ms   (0.0 s .. 41.75 ms)
variance introduced by outliers: 19% (moderately inflated)
```
</p></details>

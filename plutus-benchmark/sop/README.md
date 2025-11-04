# SOP vs Scott

This benchmark compares SOP encoded values and Scott encoded values in terms of their ExBudget usage. 

## Cases
### List 
```hs
data List x = Cons x (List x) | Nil
```

Tests `replicate` for measuring construction and `sum` for destruction.

### Big
```hs
data Big
  = BigA Integer Integer Integer Integer Integer Big
  | BigB Integer Integer Integer Integer Integer Big
  | BigC Integer Integer Integer Integer Integer Big
  | BigD Integer Integer Integer Integer Integer Big
  | BigE Integer Integer Integer Integer Integer Big
  | BigNil
```

Tests `replicate` for measuring construction and `sum` for destruction. 

`replicate` is implemented like
```hs
replicate :: Integer -> Integer -> ScottBig
replicate 0 _ = ScottBigNil
replicate n x =
  ScottBigA x x x x x
   (ScottBigB x x x x x
    (ScottBigC x x x x x
     (ScottBigD x x x x x
      (ScottBigE x x x x x (replicate (n - 1) x)))))
```

`sum` adds up all integer in the `Big` structure.

## Result
## List, replicate 50

| Category |      Scott |        SOP | % Difference |
|----------|-----------:|-----------:|-------------:|
| CPU      | 38,870,686 | 38,070,686 |       -2.06% |
| MEM      |    173,402 |    168,402 |       -2.88% |
| Size     |         62 |         51 |      -17.74% |

## List, sum

| Category |      Scott |        SOP | % Difference |
|----------|-----------:|-----------:|-------------:|
| CPU      | 24,548,500 | 18,052,500 |      -26.45% |
| MEM      |    122,000 |     81,400 |      -33.28% |
| Size     |        378 |        123 |      -67.46% |

## Big, replicate 10

| Category |     Scott |        SOP | % Difference |
|----------|----------:|-----------:|-------------:|
| CPU      | 9,880,382 | 12,280,382 |       24.24% |
| MEM      |    46,742 |     61,742 |       32.10% |
| Size     |       157 |         70 |      -55.41% |

## Big, sum

| Category |      Scott |        SOP | % Difference |
|----------|-----------:|-----------:|-------------:|
| CPU      | 76,982,100 | 57,494,100 |      -25.30% |
| MEM      |    323,600 |    201,800 |      -37.61% |
| Size     |      1,130 |        467 |      -58.67% |

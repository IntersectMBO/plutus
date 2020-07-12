# Performance of Scott Encoding vs. Explicit Datatypes in Haskell

Replicating in part the work of [Koopman, Plasmeijer, and Jansen](https://ifl2014.github.io/submissions/ifl2014_submission_13.pdf), we compare the running time of specific list operations for Scott encoded lists, and for Haskell's built in list type. Running time was measured using [Criterion](http://www.serpentine.com/criterion/tutorial.html). Benchmarks reported here were compiled with the -O flag.

The type of Scott encoded lists used is
```
newtype SList a = SList (forall r . r -> (a -> SList a -> r) -> r)

nil :: SList a
nil = SList (\n c -> n)

cons :: a -> SList a -> SList a
cons x xs = SList (\n c -> c x xs)
```

## Head of Tail of a List

We first compare the function (for Scott encoded lists)
```
headS :: SList a -> a
headS (SList l) = l undefined (\x xs -> x)

headTailS :: SList a -> a
headTailS (SList l) = l undefined (\x xs -> headS xs)
```
with the function (for built in lists)
```
headTail :: [a] -> a
headTail [] = undefined
headTail (x:xs) = head xs
```
where `m` is the size of the list:

| m | scott | builtin |
|---|-------|---------|
| 2 | 18.9ns | 5.5ns |
| 10 | 18.9ns | 5.51ns |
| 10^2 | 19.0ns | 5.77ns |
| 10^3 | 18.9ns | 5.51ns |
| 10^4 | 18.8ns | 5.51ns |
| 10^5 | 18.9ns | 5.51ns |

We find that the built in lists are ~3.4 times faster than the Scott encoded lists in this case. This is close to the difference of ~3.0 found by Koopman et al. for this comparison.

# Sum of a List of Ints

We next compare the function (for Scott encoded lists)
```
sumS :: SList Int -> Int
sumS (SList l) = l 0 (\x xs -> x + (sumS xs))
```
with the function (for built in lists)
```
directSum :: [Int] -> Int
directSum [] = 0
directSum (x:xs) = x + (directSum xs)
```
where `m` is the size of the list:

| m | scott | bulitin |
|---|-------|---------|
| 1 | 17.7ns | 7.63ns |
| 10 | 136ns | 35.2ns |
| 10^2 | 1.28us | 392ns |
| 10^3 | 13.1us | 3.88us |
| 10^4 | 196us | 93.9us |
| 10^5 | 2.9ms | 1.4ms |

We find that built in lists are, on average, ~2.7 times faster than Scott encoded lists. This is close to the difference of ~3.1 found by Koopman et al. for this comparison. 

Note that summing the list with the built in function `sum` is significantly slower than sumS. `sum` is defined as part of the typeclass `Foldable`, and the generality of its definition there likely includes some overhead. It is much fairer to compare `directSum` to `sumS`. 

## Quicksort
Finally, we compare the function `quickSortS` (for Scott encoded lists)
```
appendS :: SList a -> SList a -> SList a
appendS (SList l1) l2 = l1 l2 (\x xs -> cons x (appendS xs l2))

filterS :: (a -> Bool) -> SList a -> SList a
filterS p (SList l) = l nil (\x xs -> if p x then cons x (filterS p xs) else (filterS p xs))

quickSortS :: (Ord a) => SList a -> SList a
quickSortS cl@(SList l) = l nil (\h t -> appendS (quickSortS (filterS (\x -> x < h) cl))
                                                 (appendS (filterS (\x -> x == h) cl)
                                                          (quickSortS (filterS (\x -> h < x) cl))))
```
to the function `quickSort` (for built in lists)
```
quickSort :: (Ord a) => [a] -> [a]
quickSort [] = []
quickSort cl@(h:xs) = (quickSort (filter (\x -> x < h) cl)) ++
                      (filter (\x -> x == h) cl) ++
                      (quickSort (filter (\x -> h < x) cl))
```
where `m` is the size of the list:

| m | scott | builtin |
|---|-------|---------|
| 1 | 53.9ns | 21.8ns |
| 10 | 290ns | 141ns |
| 10^2 | 2.68us | 1.58us |
| 10^3 | 33.2us | 19.8us |
| 10^4 | 386us | 236us |
| 10^5 | 5.92ms | 4.66ms |

We find that built in lists are, on average, ~1.7 times faster than Scott encoded lists. This is close to the difference of ~2.4 found by Koopman et al.


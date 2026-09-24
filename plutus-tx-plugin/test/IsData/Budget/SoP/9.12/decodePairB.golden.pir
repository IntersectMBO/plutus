let
  data Pair | Pair_match where
    PairA : integer -> Pair
    PairB : integer -> Pair
in
\(d : data) ->
  Pair_match
    (case
       Pair
       d
       [ (\(ds : list data) -> PairA (unIData (headList {data} ds)))
       , (\(ds : list data) -> PairB (unIData (headList {data} ds))) ])
    {integer}
    (\(x : integer) -> x)
    (\(x : integer) -> addInteger 1 x)
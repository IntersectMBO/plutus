let
  data Pair | Pair_match where
    PairA : integer -> Pair
    PairB : integer -> Pair
in
\(d : data) ->
  Pair_match
    ((let
         b = list data
       in
       /\r -> \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
       {Pair}
       (unConstrData d)
       (\(index : integer) (args : list data) ->
          case
            (list data -> Pair)
            index
            [ (\(ds : list data) -> PairA (unIData (headList {data} ds)))
            , (\(ds : list data) -> PairB (unIData (headList {data} ds))) ]
            args))
    {integer}
    (\(x : integer) -> x)
    (\(x : integer) -> addInteger 1 x)
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
       /\r ->
         \(p : pair integer b) (f : integer -> b -> r) ->
           f (fstPair {integer} {b} p) (sndPair {integer} {b} p))
       {Pair}
       (unConstrData d)
       (\(index : integer) (args : list data) ->
          ifThenElse
            {all dead. list data -> Pair}
            (equalsInteger 0 index)
            (/\dead ->
               \(ds : list data) -> PairA (unIData (headList {data} ds)))
            (/\dead ->
               ifThenElse
                 {all dead. list data -> Pair}
                 (equalsInteger 1 index)
                 (/\dead ->
                    \(ds : list data) -> PairB (unIData (headList {data} ds)))
                 (/\dead -> error {list data -> Pair})
                 {list data -> Pair})
            {list data -> Pair}
            args))
    {integer}
    (\(x : integer) -> x)
    (\(x : integer) -> addInteger 1 x)
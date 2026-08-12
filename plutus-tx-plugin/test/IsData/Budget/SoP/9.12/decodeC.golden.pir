let
  data ABC | ABC_match where
    A : integer -> ABC
    B : integer -> ABC
    C : integer -> ABC
in
\(d : data) ->
  ABC_match
    ((let
         b = list data
       in
       /\r -> \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
       {ABC}
       (unConstrData d)
       (\(index : integer) (args : list data) ->
          case
            (list data -> ABC)
            index
            [ (\(ds : list data) -> A (unIData (headList {data} ds)))
            , (\(ds : list data) -> B (unIData (headList {data} ds)))
            , (\(ds : list data) -> C (unIData (headList {data} ds))) ]
            args))
    {integer}
    (\(x : integer) -> x)
    (\(x : integer) -> addInteger 100 x)
    (\(x : integer) -> addInteger 200 x)
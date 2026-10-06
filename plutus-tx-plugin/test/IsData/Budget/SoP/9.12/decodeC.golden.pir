let
  data ABC | ABC_match where
    A : integer -> ABC
    B : integer -> ABC
    C : integer -> ABC
in
\(d : data) ->
  ABC_match
    (case
       ABC
       d
       [ (\(ds : list data) -> A (unIData (headList {data} ds)))
       , (\(ds : list data) -> B (unIData (headList {data} ds)))
       , (\(ds : list data) -> C (unIData (headList {data} ds))) ])
    {integer}
    (\(x : integer) -> x)
    (\(x : integer) -> addInteger 100 x)
    (\(x : integer) -> addInteger 200 x)
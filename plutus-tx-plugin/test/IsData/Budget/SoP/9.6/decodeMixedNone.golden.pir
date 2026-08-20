let
  data Mixed | Mixed_match where
    MNone : Mixed
    MOne : integer -> Mixed
    MTwo : integer -> integer -> Mixed
in
\(d : data) ->
  Mixed_match
    (case
       Mixed
       d
       [ (\(ds : list data) -> MNone)
       , (\(ds : list data) -> MOne (unIData (headList {data} ds)))
       , (\(ds : list data) ->
            case
              Mixed
              ds
              [ (\(ds : data) (ds : list data) ->
                   MTwo (unIData ds) (unIData (headList {data} ds))) ]) ])
    {integer}
    0
    (\(x : integer) -> x)
    (\(x : integer) (y : integer) -> addInteger x y)
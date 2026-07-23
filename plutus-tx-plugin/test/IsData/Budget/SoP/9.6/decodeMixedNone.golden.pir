let
  data Mixed | Mixed_match where
    MNone : Mixed
    MOne : integer -> Mixed
    MTwo : integer -> integer -> Mixed
in
\(d : data) ->
  Mixed_match
    ((let
         b = list data
       in
       /\r -> \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
       {Mixed}
       (unConstrData d)
       (\(index : integer) (args : list data) ->
          case
            (list data -> Mixed)
            index
            [ (\(ds : list data) -> MNone)
            , (\(ds : list data) -> MOne (unIData (headList {data} ds)))
            , (\(ds : list data) ->
                 MTwo
                   (unIData (headList {data} ds))
                   (unIData (headList {data} (tailList {data} ds)))) ]
            args))
    {integer}
    0
    (\(x : integer) -> x)
    (\(x : integer) (y : integer) -> addInteger x y)
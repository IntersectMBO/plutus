let
  data Single | Single_match where
    Single : integer -> Single
in
\(d : data) ->
  Single_match
    ((let
         b = list data
       in
       /\r -> \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
       {Single}
       (unConstrData d)
       (\(index : integer) (args : list data) ->
          case
            (list data -> Single)
            index
            [(\(ds : list data) -> Single (unIData (headList {data} ds)))]
            args))
    {integer}
    (\(x : integer) -> x)
let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
\(ds : data) ->
  (let
      a = Tuple2 integer integer
    in
    \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
      case
        (Maybe a)
        d
        [ (\(ds : list data) ->
             Just {a} (`$dUnsafeFromData` (headList {data} ds)))
        , (\(ds : list data) -> Nothing {a}) ])
    (\(d : data) ->
       case
         (Tuple2 integer integer)
         d
         [ (\(ds : list data) ->
              (let
                  r = Tuple2 integer integer
                in
                \(f : data -> list data -> r) (xs : list data) -> case r xs [f])
                (\(ds : data) (ds : list data) ->
                   Tuple2
                     {integer}
                     {integer}
                     (unIData ds)
                     (unIData (headList {data} ds)))
                ds) ])
    ds
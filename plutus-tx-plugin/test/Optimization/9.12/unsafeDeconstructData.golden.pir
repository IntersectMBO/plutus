let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
in
\(ds : data) ->
  (let
      a = Tuple integer integer
    in
    \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
      case
        (Maybe a)
        (unConstrData d)
        [ (\(index : integer) (args : list data) ->
             case
               (list data -> Maybe a)
               index
               [ (\(ds : list data) ->
                    Just {a} (`$dUnsafeFromData` (headList {data} ds)))
               , (\(ds : list data) -> Nothing {a}) ]
               args) ])
    (\(d : data) ->
       case
         (Tuple integer integer)
         (unConstrData d)
         [ (\(index : integer) (args : list data) ->
              case
                (list data -> Tuple integer integer)
                index
                [ (\(ds : list data) ->
                     (let
                         r = Tuple integer integer
                       in
                       \(f : data -> list data -> r) (xs : list data) ->
                         case r xs [f])
                       (\(ds : data) (ds : list data) ->
                          Tuple2
                            {integer}
                            {integer}
                            (unIData ds)
                            (unIData (headList {data} ds)))
                       ds) ]
                args) ])
    ds
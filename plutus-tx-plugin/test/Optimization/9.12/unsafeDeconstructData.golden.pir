let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
  !casePair : all a b r. pair a b -> (a -> b -> r) -> r
    = /\a b r -> \(p : pair a b) (f : a -> b -> r) -> case r p [f]
in
\(ds : data) ->
  (let
      a = Tuple integer integer
    in
    \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
      casePair
        {integer}
        {list data}
        {Maybe a}
        (unConstrData d)
        (\(index : integer) (args : list data) ->
           case
             (list data -> Maybe a)
             index
             [ (\(ds : list data) ->
                  Just {a} (`$dUnsafeFromData` (headList {data} ds)))
             , (\(ds : list data) -> Nothing {a}) ]
             args))
    (\(d : data) ->
       casePair
         {integer}
         {list data}
         {Tuple integer integer}
         (unConstrData d)
         (\(index : integer) (args : list data) ->
            case
              (list data -> Tuple integer integer)
              index
              [ (\(ds : list data) ->
                   Tuple2
                     {integer}
                     {integer}
                     (unIData (headList {data} ds))
                     (unIData (headList {data} (tailList {data} ds)))) ]
              args))
    ds
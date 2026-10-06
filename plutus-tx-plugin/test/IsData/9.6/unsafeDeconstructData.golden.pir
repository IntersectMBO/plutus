let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !droppableUnsafeCaseList : all a r. (a -> list a -> r) -> list a -> r
    = /\a r -> \(f : a -> list a -> r) (xs : list a) -> case r xs [f]
  !head : all a. list a -> a = headList
  ~`$fUnsafeFromDataTuple2_$cunsafeFromBuiltinData` :
     all a b. (\a -> data -> a) a -> (\a -> data -> a) b -> data -> Tuple2 a b
    = /\a b ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a)
         (`$dUnsafeFromData` : (\a -> data -> a) b)
         (d : data) ->
          let
            !d : data = d
          in
          case
            (Tuple2 a b)
            d
            [ (\(ds : list data) ->
                 let
                   !ds : list data = ds
                 in
                 droppableUnsafeCaseList
                   {data}
                   {Tuple2 a b}
                   (\(ds : data) (ds : list data) ->
                      Tuple2
                        {a}
                        {b}
                        (`$dUnsafeFromData` ds)
                        (`$dUnsafeFromData` (head {data} ds)))
                   ds) ]
  ~`$fUnsafeFromDataTuple2` :
     all a b.
       (\a -> data -> a) a ->
       (\a -> data -> a) b ->
       (\a -> data -> a) (Tuple2 a b)
    = `$fUnsafeFromDataTuple2_$cunsafeFromBuiltinData`
  !unsafeDataAsI : data -> integer = unIData
  ~`$fUnsafeFromDataInteger` : (\a -> data -> a) integer = unsafeDataAsI
  ~`$dUnsafeFromData` : (\a -> data -> a) (Tuple2 integer integer)
    = `$fUnsafeFromDataTuple2`
        {integer}
        {integer}
        `$fUnsafeFromDataInteger`
        `$fUnsafeFromDataInteger`
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  ~`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData` :
     all a. (\a -> data -> a) a -> data -> Maybe a
    = /\a ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
          let
            !d : data = d
          in
          case
            (Maybe a)
            d
            [ (\(ds : list data) ->
                 let
                   !ds : list data = ds
                 in
                 Just {a} (`$dUnsafeFromData` (head {data} ds)))
            , (\(ds : list data) -> Nothing {a}) ]
  ~`$fUnsafeFromDataMaybe` :
     all a. (\a -> data -> a) a -> (\a -> data -> a) (Maybe a)
    = `$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
  ~`$dUnsafeFromData` : (\a -> data -> a) (Maybe (Tuple2 integer integer))
    = `$fUnsafeFromDataMaybe` {Tuple2 integer integer} `$dUnsafeFromData`
  ~unsafeFromBuiltinData : all a. (\a -> data -> a) a -> data -> a
    = /\a -> \(v : (\a -> data -> a) a) -> v
in
\(ds : data) ->
  let
    !ds : data = ds
  in
  unsafeFromBuiltinData {Maybe (Tuple2 integer integer)} `$dUnsafeFromData` ds
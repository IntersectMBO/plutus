let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !casePair : all a b r. pair a b -> (a -> b -> r) -> r
    = /\a b r -> \(p : pair a b) (f : a -> b -> r) -> case r p [f]
  !head : all a. list a -> a = headList
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
  !tail : all a. list a -> list a = tailList
  ~wrapTail : all a. list a -> list a = tail
  ~`$fUnsafeFromDataTuple2_$cunsafeFromBuiltinData` :
     all a b. (\a -> data -> a) a -> (\a -> data -> a) b -> data -> Tuple2 a b
    = /\a b ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a)
         (`$dUnsafeFromData` : (\a -> data -> a) b)
         (d : data) ->
          let
            !d : data = d
          in
          casePair
            {integer}
            {list data}
            {Tuple2 a b}
            (unsafeDataAsConstr d)
            (\(index : integer) ->
               let
                 !index : integer = index
               in
               \(args : list data) ->
                 let
                   !args : list data = args
                 in
                 case
                   (list data -> Tuple2 a b)
                   index
                   [ (\(ds : list data) ->
                        let
                          !ds : list data = ds
                        in
                        Tuple2
                          {a}
                          {b}
                          (`$dUnsafeFromData` (head {data} ds))
                          (`$dUnsafeFromData`
                             (head {data} (wrapTail {data} ds)))) ]
                   args)
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
          casePair
            {integer}
            {list data}
            {Maybe a}
            (unsafeDataAsConstr d)
            (\(index : integer) ->
               let
                 !index : integer = index
               in
               \(args : list data) ->
                 let
                   !args : list data = args
                 in
                 case
                   (list data -> Maybe a)
                   index
                   [ (\(ds : list data) ->
                        let
                          !ds : list data = ds
                        in
                        Just {a} (`$dUnsafeFromData` (head {data} ds)))
                   , (\(ds : list data) -> Nothing {a}) ]
                   args)
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
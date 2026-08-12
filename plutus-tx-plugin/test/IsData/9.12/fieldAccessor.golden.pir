let
  !mkI : integer -> data = iData
  ~`$fToDataInteger_$ctoBuiltinData` : integer -> data
    = \(i : integer) -> let !i : integer = i in mkI i
  ~`$fToDataInteger` : (\a -> a -> data) integer
    = `$fToDataInteger_$ctoBuiltinData`
  !unsafeDataAsI : data -> integer = unIData
  ~`$fUnsafeFromDataInteger` : (\a -> data -> a) integer = unsafeDataAsI
  !droppableUnsafeCaseList : all a r. (a -> list a -> r) -> list a -> r
    = /\a r -> \(f : a -> list a -> r) (xs : list a) -> case r xs [f]
  !snd : all a b. pair a b -> b
    = /\a b -> \(x : pair a b) -> case b x [(\(l : a) (r : b) -> r)]
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
  ~wrapUnsafeDataAsConstr : data -> pair integer (list data)
    = unsafeDataAsConstr
  ~x : all a. (\a -> a -> data) a -> (\a -> data -> a) a -> (\a -> data) a -> a
    = /\a ->
        \(`$dToData` : (\a -> a -> data) a)
         (`$dUnsafeFromData` : (\a -> data -> a) a)
         (ds : (\a -> data) a) ->
          let
            !nt : data = ds
          in
          droppableUnsafeCaseList
            {data}
            {a}
            (\(ds : data) ->
               let
                 ~ds : a = `$dUnsafeFromData` ds
               in
               \(ds : list data) -> ds)
            (snd {integer} {list data} (wrapUnsafeDataAsConstr nt))
in
\(r : (\a -> data) integer) ->
  let
    !nt : data = r
  in
  x {integer} `$fToDataInteger` `$fUnsafeFromDataInteger` nt
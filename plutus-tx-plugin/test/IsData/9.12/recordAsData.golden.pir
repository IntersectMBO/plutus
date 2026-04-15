let
  !mkCons : all a. a -> list a -> list a = mkCons
  !mkConstr : integer -> list data -> data = constrData
  !mkI : integer -> data = iData
  !mkNilData : unit -> list data = mkNilData
  !unitval : unit = ()
  ~`$bRecordConstructor` :
     all a.
       (\a -> a -> data) a ->
       (\a -> data -> a) a ->
       a ->
       integer ->
       (\a -> data) a
    = /\a ->
        \(`$dToData` : (\a -> a -> data) a)
         (`$dUnsafeFromData` : (\a -> data -> a) a)
         (x_ : a) ->
          let
            !x_ : a = x_
          in
          \(y_ : integer) ->
            let
              !y_ : integer = y_
            in
            mkConstr
              0
              (mkCons
                 {data}
                 (`$dToData` x_)
                 (mkCons {data} (mkI y_) (mkNilData unitval)))
  ~`$fToDataInteger_$ctoBuiltinData` : integer -> data
    = \(i : integer) -> let !i : integer = i in mkI i
  ~`$fToDataInteger` : (\a -> a -> data) integer
    = `$fToDataInteger_$ctoBuiltinData`
  !unsafeDataAsI : data -> integer = unIData
  ~`$fUnsafeFromDataInteger` : (\a -> data -> a) integer = unsafeDataAsI
in
`$bRecordConstructor` {integer} `$fToDataInteger` `$fUnsafeFromDataInteger` 1 2
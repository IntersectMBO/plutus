let
  !mkI : integer -> data = iData
  ~`$fToDataInteger_$ctoBuiltinData` : integer -> data
    = \(i : integer) -> let !i : integer = i in mkI i
  ~`$fToDataInteger` : (\a -> a -> data) integer
    = `$fToDataInteger_$ctoBuiltinData`
  !mkCons : all a. a -> list a -> list a = mkCons
  !mkConstr : integer -> list data -> data = constrData
  !mkNilData : unit -> list data = mkNilData
  ~toBuiltinData : all a. (\a -> a -> data) a -> a -> data
    = /\a -> \(v : (\a -> a -> data) a) -> v
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
                 (toBuiltinData {a} `$dToData` x_)
                 (mkCons
                    {data}
                    (toBuiltinData {integer} `$fToDataInteger` y_)
                    (mkNilData unitval)))
  !unsafeDataAsI : data -> integer = unIData
  ~`$fUnsafeFromDataInteger` : (\a -> data -> a) integer = unsafeDataAsI
in
`$bRecordConstructor` {integer} `$fToDataInteger` `$fUnsafeFromDataInteger` 1 2
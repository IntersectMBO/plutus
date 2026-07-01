let
  data Unit | Unit_match where
    Unit : Unit
  !mkCons : all a. a -> list a -> list a = mkCons
  !mkConstr : integer -> list data -> data = constrData
  !mkNilData : unit -> list data = mkNilData
  !unitval : unit = ()
  ~`$bFirstC` : Unit -> data
    = \(arg0_ : Unit) ->
        mkConstr
          0
          (mkCons {data} (mkConstr 0 (mkNilData unitval)) (mkNilData unitval))
  ~fail : unit -> data = \(ds : unit) -> `$bFirstC` Unit
  !mkI : integer -> data = iData
  ~`$bSecondC` : integer -> data
    = \(arg0_ : integer) ->
        let
          !arg0_ : integer = arg0_
        in
        mkConstr 1 (mkCons {data} (mkI arg0_) (mkNilData unitval))
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  ~`$fEqInteger` : (\a -> a -> a -> bool) integer = equalsInteger
  ~`$fToDataInteger_$ctoBuiltinData` : integer -> data
    = \(i : integer) -> let !i : integer = i in mkI i
  ~`$fToDataInteger` : (\a -> a -> data) integer
    = `$fToDataInteger_$ctoBuiltinData`
  !unsafeDataAsI : data -> integer = unIData
  ~`$fUnsafeFromDataInteger` : (\a -> data -> a) integer = unsafeDataAsI
  !head : all a. list a -> a = headList
  !snd : all a b. pair a b -> b
    = /\a b -> \(x : pair a b) -> case b x [(\(l : a) (r : b) -> r)]
  !tail : all a. list a -> list a = tailList
  ~wrapTail : all a. list a -> list a = tail
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
  ~wrapUnsafeDataAsConstr : data -> pair integer (list data)
    = unsafeDataAsConstr
  ~`$mRecordConstructor` :
     all r a.
       (\a -> a -> data) a ->
       (\a -> data -> a) a ->
       (\a -> data) a ->
       (a -> integer -> r) ->
       (unit -> r) ->
       r
    = /\r a ->
        \(`$dToData` : (\a -> a -> data) a)
         (`$dUnsafeFromData` : (\a -> data -> a) a)
         (scrut : (\a -> data) a) ->
          let
            !nt : data = scrut
          in
          \(cont : a -> integer -> r) ->
            let
              !cont : a -> integer -> r = cont
            in
            \(fail : unit -> r) ->
              let
                !l : list data
                  = snd {integer} {list data} (wrapUnsafeDataAsConstr nt)
              in
              cont
                (`$dUnsafeFromData` (head {data} l))
                (unsafeDataAsI (head {data} (wrapTail {data} l)))
  ~`==` : all a. (\a -> a -> a -> bool) a -> a -> a -> bool
    = /\a -> \(v : (\a -> a -> a -> bool) a) -> v
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
in
\(ds : (\a -> data) integer) ->
  let
    !nt : data = ds
  in
  `$mRecordConstructor`
    {data}
    {integer}
    `$fToDataInteger`
    `$fUnsafeFromDataInteger`
    nt
    (\(a : integer) (b : integer) ->
       case
         (all dead. data)
         (`==` {integer} `$fEqInteger` a 3)
         [ (/\dead -> fail ())
         , (/\dead ->
              case
                (all dead. data)
                (`==` {integer} `$fEqInteger` b 4)
                [(/\dead -> fail ()), (/\dead -> `$bSecondC` (addInteger a b))]
                {all dead. dead}) ]
         {all dead. dead})
    (\(void : unit) -> fail ())
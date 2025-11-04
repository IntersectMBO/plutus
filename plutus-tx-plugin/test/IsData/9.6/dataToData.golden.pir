let
  data Unit | Unit_match where
    Unit : Unit
  !mkConstr : integer -> list data -> data = constrData
  !mkNilData : unit -> list data = mkNilData
  !unitval : unit = ()
  ~`$fToDataUnit_$ctoBuiltinData` : Unit -> data
    = \(ds : Unit) -> mkConstr 0 (mkNilData unitval)
  ~`$fToDataUnit` : (\a -> a -> data) Unit = `$fToDataUnit_$ctoBuiltinData`
  !mkCons : all a. a -> list a -> list a = mkCons
  ~toBuiltinData : all a. (\a -> a -> data) a -> a -> data
    = /\a -> \(v : (\a -> a -> data) a) -> v
  ~`$bFirstC` : Unit -> data
    = \(arg0_ : Unit) ->
        let
          !arg0_ : Unit = arg0_
        in
        mkConstr
          0
          (mkCons
             {data}
             (toBuiltinData {Unit} `$fToDataUnit` arg0_)
             (mkNilData unitval))
  ~fail : unit -> data = \(ds : unit) -> `$bFirstC` Unit
  !mkI : integer -> data = iData
  ~`$fToDataInteger_$ctoBuiltinData` : integer -> data
    = \(i : integer) -> let !i : integer = i in mkI i
  ~`$fToDataInteger` : (\a -> a -> data) integer
    = `$fToDataInteger_$ctoBuiltinData`
  ~`$bSecondC` : integer -> data
    = \(arg0_ : integer) ->
        let
          !arg0_ : integer = arg0_
        in
        mkConstr
          1
          (mkCons
             {data}
             (toBuiltinData {integer} `$fToDataInteger` arg0_)
             (mkNilData unitval))
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  ~`$fEqInteger` : (\a -> a -> a -> bool) integer = equalsInteger
  !unsafeDataAsI : data -> integer = unIData
  ~`$fUnsafeFromDataInteger` : (\a -> data -> a) integer = unsafeDataAsI
  !snd : all a b. pair a b -> b
    = /\a b -> \(x : pair a b) -> case b x [(\(l : a) (r : b) -> r)]
  ~unsafeFromBuiltinData : all a. (\a -> data -> a) a -> data -> a
    = /\a -> \(v : (\a -> data -> a) a) -> v
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
  ~wrapUnsafeDataAsConstr : data -> pair integer (list data)
    = unsafeDataAsConstr
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !head : all a. list a -> a = headList
  !tail : all a. list a -> list a = tailList
  ~wrapTail : all a. list a -> list a = tail
  ~wrapUnsafeUncons : all a. list a -> Tuple2 a (list a)
    = /\a ->
        \(l : list a) ->
          let
            !l : list a = l
          in
          Tuple2 {a} {list a} (head {a} l) (wrapTail {a} l)
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
              Tuple2_match
                {data}
                {list data}
                (wrapUnsafeUncons
                   {data}
                   (snd {integer} {list data} (wrapUnsafeDataAsConstr nt)))
                {r}
                (\(ds : data) (ds : list data) ->
                   cont
                     (unsafeFromBuiltinData {a} `$dUnsafeFromData` ds)
                     (unsafeFromBuiltinData
                        {integer}
                        `$fUnsafeFromDataInteger`
                        (head {data} ds)))
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
let
  ~defaultBody : data = (/\e -> error {e}) {data}
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
  ~id : all a. a -> a = /\a -> \(x : a) -> x
  ~`$fToDataBuiltinData` : (\a -> a -> data) data = id {data}
  ~`$ctoBuiltinData` : data -> data = toBuiltinData {data} `$fToDataBuiltinData`
  ~`$fToDataSecretlyData` : (\a -> a -> data) data = `$ctoBuiltinData`
  ~`$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData` : data -> data
    = \(d : data) -> d
  ~`$fUnsafeFromDataBuiltinData` : (\a -> data -> a) data
    = `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
  ~unsafeFromBuiltinData : all a. (\a -> data -> a) a -> data -> a
    = /\a -> \(v : (\a -> data -> a) a) -> v
  ~`$cunsafeFromBuiltinData` : data -> data
    = unsafeFromBuiltinData {data} `$fUnsafeFromDataBuiltinData`
  ~`$fUnsafeFromDataSecretlyData` : (\a -> data -> a) data
    = `$cunsafeFromBuiltinData`
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  ~`$fEqInteger` : (\a -> a -> a -> bool) integer = equalsInteger
  ~`==` : all a. (\a -> a -> a -> bool) a -> a -> a -> bool
    = /\a -> \(v : (\a -> a -> a -> bool) a) -> v
  !head : all a. list a -> a = headList
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
  !fst : all a b. pair a b -> a
    = /\a b -> \(x : pair a b) -> case a x [(\(l : a) (r : b) -> l)]
  !snd : all a b. pair a b -> b
    = /\a b -> \(x : pair a b) -> case b x [(\(l : a) (r : b) -> r)]
  ~pairToPair : all a b. pair a b -> Tuple a b
    = /\a b ->
        \(tup : pair a b) ->
          let
            !tup : pair a b = tup
          in
          Tuple2 {a} {b} (fst {a} {b} tup) (snd {a} {b} tup)
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
  ~wrapUnsafeDataAsConstr : data -> pair integer (list data)
    = unsafeDataAsConstr
  ~`$mJustD` :
     all r a.
       (\a -> a -> data) a ->
       (\a -> data -> a) a ->
       (\a -> data) a ->
       (a -> r) ->
       (unit -> r) ->
       r
    = /\r a ->
        \(`$dToData` : (\a -> a -> data) a)
         (`$dUnsafeFromData` : (\a -> data -> a) a)
         (scrut : (\a -> data) a) ->
          let
            !nt : data = scrut
          in
          \(cont : a -> r) ->
            let
              !cont : a -> r = cont
            in
            \(fail : unit -> r) ->
              let
                !fail : unit -> r = fail
              in
              Tuple_match
                {integer}
                {list data}
                (pairToPair {integer} {list data} (wrapUnsafeDataAsConstr nt))
                {r}
                (\(ds : integer) (ds : list data) ->
                   case
                     (all dead. r)
                     (`==` {integer} `$fEqInteger` 0 ds)
                     [ (/\dead -> fail ())
                     , (/\dead ->
                          cont
                            (unsafeFromBuiltinData
                               {a}
                               `$dUnsafeFromData`
                               (head {data} ds))) ]
                     {all dead. dead})
  ~`$mNothingD` : all r a. (\a -> data) a -> (unit -> r) -> (unit -> r) -> r
    = /\r a ->
        \(scrut : (\a -> data) a) ->
          let
            !nt : data = scrut
          in
          \(cont : unit -> r) ->
            let
              !cont : unit -> r = cont
            in
            \(fail : unit -> r) ->
              let
                !fail : unit -> r = fail
              in
              Tuple_match
                {integer}
                {list data}
                (pairToPair {integer} {list data} (wrapUnsafeDataAsConstr nt))
                {r}
                (\(ds : integer) (ds : list data) ->
                   case
                     (all dead. r)
                     (`==` {integer} `$fEqInteger` 1 ds)
                     [(/\dead -> fail ()), (/\dead -> cont ())]
                     {all dead. dead})
in
\(ds : (\a -> data) data) ->
  let
    !nt : data = ds
  in
  `$mJustD`
    {data}
    {data}
    `$fToDataSecretlyData`
    `$fUnsafeFromDataSecretlyData`
    nt
    (\(a : data) -> a)
    (\(void : unit) ->
       `$mNothingD`
         {data}
         {data}
         nt
         (\(void : unit) -> `$bFirstC` Unit)
         (\(void : unit) ->
            Unit_match ((/\e -> error {e}) {Unit}) {data} defaultBody))
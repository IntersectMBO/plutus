let
  ~defaultBody : data = (/\e -> error {e}) {data}
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
  ~id : all a. a -> a = /\a -> \(x : a) -> x
  ~`$fToDataSecretlyData` : (\a -> a -> data) data = id {data}
  ~`$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData` : data -> data
    = \(d : data) -> d
  ~`$fUnsafeFromDataSecretlyData` : (\a -> data -> a) data
    = `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
  !equalsInteger : integer -> integer -> bool = equalsInteger
  !fst : all a b. pair a b -> a
    = /\a b -> \(x : pair a b) -> case a x [(\(l : a) (r : b) -> l)]
  !head : all a. list a -> a = headList
  !snd : all a b. pair a b -> b
    = /\a b -> \(x : pair a b) -> case b x [(\(l : a) (r : b) -> r)]
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
                !tup : pair integer (list data) = wrapUnsafeDataAsConstr nt
              in
              case
                (all dead. r)
                (let
                  !y : integer = fst {integer} {list data} tup
                in
                equalsInteger 0 y)
                [ (/\dead -> fail ())
                , (/\dead ->
                     cont
                       (`$dUnsafeFromData`
                          (head {data} (snd {integer} {list data} tup)))) ]
                {all dead. dead}
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
                !tup : pair integer (list data) = wrapUnsafeDataAsConstr nt
              in
              case
                (all dead. r)
                (let
                  !y : integer = fst {integer} {list data} tup
                in
                equalsInteger 1 y)
                [(/\dead -> fail ()), (/\dead -> cont ())]
                {all dead. dead}
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
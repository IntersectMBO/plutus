let
  !mkI : integer -> data = iData
  ~`$fToDataInteger_$ctoBuiltinData` : integer -> data
    = \(i : integer) -> let !i : integer = i in mkI i
  ~`$fToDataInteger` : (\a -> a -> data) integer
    = `$fToDataInteger_$ctoBuiltinData`
  !unsafeDataAsI : data -> integer = unIData
  ~`$fUnsafeFromDataInteger` : (\a -> data -> a) integer = unsafeDataAsI
  !snd : all a b. pair a b -> b
    = /\a b -> \(x : pair a b) -> case b x [(\(l : a) (r : b) -> r)]
  ~unsafeFromBuiltinData : all a. (\a -> data -> a) a -> data -> a
    = /\a -> \(v : (\a -> data -> a) a) -> v
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
  ~wrapUnsafeDataAsConstr : data -> pair integer (list data)
    = unsafeDataAsConstr
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
  !head : all a. list a -> a = headList
  !tail : all a. list a -> list a = tailList
  ~wrapTail : all a. list a -> list a = tail
  ~wrapUnsafeUncons : all a. list a -> Tuple a (list a)
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
              Tuple_match
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
  ~x : all a. (\a -> a -> data) a -> (\a -> data -> a) a -> (\a -> data) a -> a
    = /\a ->
        \(`$dToData` : (\a -> a -> data) a)
         (`$dUnsafeFromData` : (\a -> data -> a) a)
         (ds : (\a -> data) a) ->
          let
            !nt : data = ds
          in
          `$mRecordConstructor`
            {a}
            {a}
            `$dToData`
            `$dUnsafeFromData`
            nt
            (\(ds : a) (ds : integer) -> ds)
            (\(void : unit) -> (/\e -> error {e}) {a})
in
\(r : (\a -> data) integer) ->
  let
    !nt : data = r
  in
  x {integer} `$fToDataInteger` `$fUnsafeFromDataInteger` nt
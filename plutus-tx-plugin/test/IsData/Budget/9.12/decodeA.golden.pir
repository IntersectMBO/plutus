let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~`$fAdditiveSemigroupInteger` : (\a -> a -> a -> a) integer = addInteger
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~indexTooLargeError : string = "PT7"
  !lessThanInteger : integer -> integer -> bool = lessThanInteger
  ~negativeIndexError : string = "PT6"
  !subtractInteger : integer -> integer -> integer = subtractInteger
  data Unit | Unit_match where
    Unit : Unit
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !trace : all a. string -> a -> a = trace
  !unitval : unit = ()
  ~traceError : all a. string -> a
    = /\a ->
        \(str : string) ->
          let
            !str : string = str
            !x : Unit = trace {Unit} str Unit
          in
          error {a} unitval
  ~`!!` : all a. List a -> integer -> a
    = /\a ->
        letrec
          ~go : integer -> List a -> a
            = \(ds : integer) ->
                let
                  !ds : integer = ds
                in
                \(ds : List a) ->
                  List_match
                    {a}
                    ds
                    {all dead. a}
                    (/\dead -> traceError {a} indexTooLargeError)
                    (\(x : a) (xs : List a) ->
                       /\dead ->
                         ifThenElse
                           {all dead. a}
                           (equalsInteger ds 0)
                           (/\dead -> x)
                           (/\dead -> go (subtractInteger ds 1) xs)
                           {all dead. dead})
                    {all dead. dead}
        in
        \(ds : List a) ->
          let
            !ds : List a = ds
          in
          \(n : integer) ->
            let
              !n : integer = n
            in
            ifThenElse
              {all dead. a}
              (lessThanInteger n 0)
              (/\dead -> traceError {a} negativeIndexError)
              (/\dead -> go n ds)
              {all dead. dead}
  data ABC | ABC_match where
    A : integer -> ABC
    B : integer -> ABC
    C : integer -> ABC
  ~`$WA` : integer -> ABC
    = \(conrep : integer) -> let !conrep : integer = conrep in A conrep
  ~`$WB` : integer -> ABC
    = \(conrep : integer) -> let !conrep : integer = conrep in B conrep
  ~`$WC` : integer -> ABC
    = \(conrep : integer) -> let !conrep : integer = conrep in C conrep
  ~build : all a. (all b. (a -> b -> b) -> b -> b) -> List a
    = /\a ->
        \(g : all b. (a -> b -> b) -> b -> b) ->
          g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a})
  !casePair : all a b r. pair a b -> (a -> b -> r) -> r
    = /\a b r ->
        \(p : pair a b) (f : a -> b -> r) ->
          f (fstPair {a} {b} p) (sndPair {a} {b} p)
  !head : all a. list a -> a = headList
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
  !unsafeDataAsI : data -> integer = unIData
  ~`$fUnsafeFromDataABC_$cunsafeFromBuiltinData` : data -> ABC
    = \(d : data) ->
        let
          !d : data = d
        in
        casePair
          {integer}
          {list data}
          {ABC}
          (unsafeDataAsConstr d)
          (\(index : integer) ->
             let
               !index : integer = index
             in
             \(args : list data) ->
               let
                 !args : list data = args
               in
               `!!`
                 {list data -> ABC}
                 (build
                    {list data -> ABC}
                    (/\a ->
                       \(c : (list data -> ABC) -> a -> a) (n : a) ->
                         c
                           (\(ds : list data) ->
                              let
                                !ds : list data = ds
                              in
                              `$WA` (unsafeDataAsI (head {data} ds)))
                           (c
                              (\(ds : list data) ->
                                 let
                                   !ds : list data = ds
                                 in
                                 `$WB` (unsafeDataAsI (head {data} ds)))
                              (c
                                 (\(ds : list data) ->
                                    let
                                      !ds : list data = ds
                                    in
                                    `$WC` (unsafeDataAsI (head {data} ds)))
                                 n))))
                 index
                 args)
  ~`$fUnsafeFromDataABC` : (\a -> data -> a) ABC
    = `$fUnsafeFromDataABC_$cunsafeFromBuiltinData`
  ~`+` : all a. (\a -> a -> a -> a) a -> a -> a -> a
    = /\a -> \(v : (\a -> a -> a -> a) a) -> v
  ~unsafeFromBuiltinData : all a. (\a -> data -> a) a -> data -> a
    = /\a -> \(v : (\a -> data -> a) a) -> v
in
\(d : data) ->
  let
    !d : data = d
  in
  ABC_match
    (unsafeFromBuiltinData {ABC} `$fUnsafeFromDataABC` d)
    {integer}
    (\(x : integer) -> x)
    (\(x : integer) -> `+` {integer} `$fAdditiveSemigroupInteger` x 100)
    (\(x : integer) -> `+` {integer} `$fAdditiveSemigroupInteger` x 200)
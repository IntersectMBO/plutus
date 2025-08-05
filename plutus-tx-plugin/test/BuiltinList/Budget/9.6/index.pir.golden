let
  ~builtinListIndexTooLargeError : string = "PT22"
  ~builtinListNegativeIndexError : string = "PT21"
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  !drop : all a. integer -> list a -> list a = dropList
  !lessThanInteger : integer -> integer -> bool = lessThanInteger
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
  ~`!!` : all a. list a -> integer -> a
    = /\a ->
        \(xs : list a) ->
          let
            !xs : list a = xs
          in
          \(i : integer) ->
            let
              !i : integer = i
            in
            case
              (all dead. a)
              (lessThanInteger i 0)
              [ (/\dead ->
                   let
                     !l : list a = drop {a} i xs
                   in
                   caseList'
                     {a}
                     {Unit -> Unit -> a}
                     (\(_ann : Unit) ->
                        traceError {Unit -> a} builtinListIndexTooLargeError)
                     (\(x : a) ->
                        let
                          !x : a = x
                        in
                        \(xs : list a) (ds : Unit) (_ann : Unit) -> x)
                     l
                     Unit
                     Unit)
              , (/\dead -> traceError {a} builtinListNegativeIndexError) ]
              {all dead. dead}
in
\(xs : list integer) -> let !xs : list integer = xs in `!!` {integer} xs 5
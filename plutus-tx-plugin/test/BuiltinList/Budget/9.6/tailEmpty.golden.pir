let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  ~mkNil : all arep. (\arep -> list arep) arep -> list arep
    = /\arep -> \(v : (\arep -> list arep) arep) -> v
  ~empty : all a. (\arep -> list arep) a -> list a = mkNil
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~lastEmptyBuiltinListError : string = "PT25"
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
  ~tail : all a. list a -> list a
    = /\a ->
        \(eta : list a) ->
          let
            !l : list a = eta
          in
          caseList'
            {a}
            {Unit -> list a}
            (\(ds : Unit) -> traceError {list a} lastEmptyBuiltinListError)
            (\(x : a) (xs : list a) ->
               let
                 !xs : list a = xs
               in
               \(ds : Unit) -> xs)
            l
            Unit
in
\(ds : list integer) -> tail {integer} (empty {integer} `$fMkNilInteger`)
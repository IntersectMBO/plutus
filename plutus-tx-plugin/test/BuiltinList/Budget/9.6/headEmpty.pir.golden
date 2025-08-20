let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  ~mkNil : all arep. (\arep -> list arep) arep -> list arep
    = /\arep -> \(v : (\arep -> list arep) arep) -> v
  ~empty : all a. (\arep -> list arep) a -> list a = mkNil
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~headEmptyBuiltinListError : string = "PT23"
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
  ~head : all a. list a -> a
    = /\a ->
        \(eta : list a) ->
          let
            !l : list a = eta
          in
          caseList'
            {a}
            {Unit -> a}
            (\(ds : Unit) -> traceError {a} headEmptyBuiltinListError)
            (\(x : a) -> let !x : a = x in \(xs : list a) (ds : Unit) -> x)
            l
            Unit
in
\(ds : list integer) -> head {integer} (empty {integer} `$fMkNilInteger`)
let
  !trace : all a. string -> a -> a = trace
  ~trace : all a. string -> a -> a = trace
  data Unit | Unit_match where
    Unit : Unit
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !unitval : unit = ()
  ~traceError : all a. string -> a
    = /\a ->
        \(str : string) ->
          let
            !str : string = str
            !x : Unit = trace {Unit} str Unit
          in
          error {a} unitval
in
\(ds : bool) ->
  let
    !ds : bool = ds
  in
  case
    (all dead. Unit)
    ds
    [(/\dead -> traceError {Unit} "no"), (/\dead -> trace {Unit} "yes" Unit)]
    {all dead. dead}
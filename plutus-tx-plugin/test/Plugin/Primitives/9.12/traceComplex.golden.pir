let
  !trace : all a. string -> a -> a = trace
  ~trace : all a. string -> a -> a = trace
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !unitval : unit = ()
  ~traceError : all a. string -> a
    = /\a ->
        \(str : string) ->
          let
            !str : string = str
            !x : unit = trace {unit} str ()
          in
          error {a} unitval
in
\(ds : bool) ->
  let
    !ds : bool = ds
  in
  case
    (all dead. unit)
    ds
    [(/\dead -> traceError {unit} "no"), (/\dead -> trace {unit} "yes" ())]
    {all dead. dead}
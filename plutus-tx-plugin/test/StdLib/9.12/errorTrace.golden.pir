let
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !trace : all a. string -> a -> a = trace
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
traceError {integer} ""
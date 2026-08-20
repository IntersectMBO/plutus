let
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !unitval : unit = ()
  ~error : all a. unit -> a = /\a -> \(x : unit) -> error {a} unitval
in
error {integer}
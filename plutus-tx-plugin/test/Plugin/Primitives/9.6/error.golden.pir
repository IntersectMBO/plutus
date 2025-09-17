let
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !unitval : unit = ()
  Unit = all a. a -> a
  ~error : all a. Unit -> a = /\a -> \(x : Unit) -> error {a} unitval
in
error {integer}
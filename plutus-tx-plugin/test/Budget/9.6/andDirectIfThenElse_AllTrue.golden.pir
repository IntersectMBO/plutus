(let
    !ifThenElse : all a. bool -> a -> a -> a
      = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
  in
  \(x : integer) (y : integer) (z : integer) ->
    ifThenElse
      {unit -> bool}
      (lessThanInteger x 100)
      (\(ds : unit) ->
         ifThenElse
           {unit -> bool}
           (lessThanInteger y 100)
           (\(ds : unit) -> lessThanInteger z 100)
           (\(ds : unit) -> False)
           ())
      (\(ds : unit) -> False)
      ())
  50
  60
  70
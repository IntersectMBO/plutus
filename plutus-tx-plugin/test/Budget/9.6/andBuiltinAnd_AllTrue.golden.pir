(\(x : integer) (y : integer) (z : integer) ->
   let
     !b : bool = lessThanInteger x 100
     !b : bool
       = let
         !b : bool = lessThanInteger y 100
         !b : bool = lessThanInteger z 100
       in
       case (unit -> bool) b [(\(ds : unit) -> False), (\(ds : unit) -> b)] ()
   in
   case (unit -> bool) b [(\(ds : unit) -> False), (\(ds : unit) -> b)] ())
  50
  60
  70
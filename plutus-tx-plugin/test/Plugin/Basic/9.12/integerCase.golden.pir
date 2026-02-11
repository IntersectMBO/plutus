let
  ~ds : integer = 2
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  !integerNegate : integer -> integer = \(x : integer) -> subtractInteger 0 x
in
case
  (all dead. integer)
  (equalsInteger ds 1)
  [ (/\dead ->
       case
         (all dead. integer)
         (equalsInteger ds 2)
         [(/\dead -> integerNegate 1), (/\dead -> 100)]
         {all dead. dead})
  , (/\dead -> 42) ]
  {all dead. dead}
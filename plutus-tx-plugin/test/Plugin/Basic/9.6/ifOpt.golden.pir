let
  !divideInteger : integer -> integer -> integer = divideInteger
  ~divideInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in divideInteger x y
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  !wild : bool = equalsInteger (divideInteger 1 0) 0
in
1
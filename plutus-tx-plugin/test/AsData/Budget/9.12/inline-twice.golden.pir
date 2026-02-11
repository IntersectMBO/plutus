let
  !multiplyInteger : integer -> integer -> integer
    = \(x : integer) (y : integer) -> multiplyInteger x y
in
\(x : integer) (y : integer) (z : integer) ->
  multiplyInteger
    (multiplyInteger (addInteger x x) (addInteger y y))
    (addInteger z z)
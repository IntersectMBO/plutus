\(x : integer) ->
  let
    !square : integer = multiplyInteger x x
  in
  addInteger (addInteger square square) (multiplyInteger x x)
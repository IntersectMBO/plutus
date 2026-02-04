letrec
  !factorial : integer -> integer
    = \(x : integer) ->
        case
          (all dead. integer)
          (equalsInteger 0 x)
          [ (/\dead -> multiplyInteger x (factorial (subtractInteger x 1)))
          , (/\dead -> 1) ]
          {all dead. dead}
in
let
  !multiplyInteger : integer -> integer -> integer
    = \(x : integer) (y : integer) -> multiplyInteger x y
in
\(x : integer) (y : integer) (z : integer) ->
  multiplyInteger (multiplyInteger (factorial x) (factorial y)) (factorial z)
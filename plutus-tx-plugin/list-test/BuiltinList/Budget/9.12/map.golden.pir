letrec
  !go : list integer -> list integer
    = (let
          r = list integer
        in
        \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
          case r xs [f, z])
        []
        (\(x : integer) (xs : list integer) ->
           mkCons {integer} (addInteger 1 x) (go xs))
in
go
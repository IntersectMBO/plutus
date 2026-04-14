letrec
  !go : integer -> list integer -> list integer
    = \(i : integer) ->
        (let
            r = list integer
          in
          \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
            case r xs [f, z])
          []
          (\(x : integer) (xs : list integer) ->
             let
               !indices : list integer = go (addInteger 1 i) xs
             in
             case
               (all dead. list integer)
               (case bool (equalsInteger 0 (modInteger x 2)) [True, False])
               [(/\dead -> indices), (/\dead -> mkCons {integer} i indices)]
               {all dead. dead})
in
\(xs : list integer) -> go 0 xs
letrec
  !go : list integer -> list integer
    = \(xs : list integer) ->
        (let
            r = list integer
          in
          \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
            case r xs [f, z])
          xs
          (\(x : integer) (xs' : list integer) ->
             case
               (all dead. list integer)
               (lessThanInteger x 5)
               [(/\dead -> xs), (/\dead -> go xs')]
               {all dead. dead})
          xs
in
\(xs : list integer) -> go xs
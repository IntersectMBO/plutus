\(xs : list integer) ->
  (letrec
      !go : list integer -> list integer
        = (let
              r = list integer
            in
            \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
              case r xs [f, z])
            []
            (\(x : integer) (xs : list integer) ->
               let
                 !xs : list integer = go xs
               in
               case
                 (all dead. list integer)
                 (equalsInteger 0 (modInteger x 2))
                 [(/\dead -> xs), (/\dead -> mkCons {integer} x xs)]
                 {all dead. dead})
    in
    go)
    xs
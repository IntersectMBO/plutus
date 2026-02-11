letrec
  !go : list integer -> list integer -> list integer
    = \(xs : list integer) (ys : list integer) ->
        case
          (list integer)
          xs
          [ (\(x : integer) (xs' : list integer) ->
               case
                 (list integer)
                 ys
                 [ (\(y : integer) (ys' : list integer) ->
                      mkCons {integer} (addInteger x y) (go xs' ys'))
                 , [] ])
          , [] ]
in
\(xs : list integer) -> go xs xs
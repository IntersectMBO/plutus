letrec
  !go : list integer -> integer
    = \(xs : list integer) ->
        case
          integer
          xs
          [(\(x : integer) (xs : list integer) -> addInteger x (go xs)), 0]
in
\(xs : list integer) -> go xs
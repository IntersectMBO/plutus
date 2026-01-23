letrec
  !go : integer -> list integer -> integer
    = \(acc : integer) (xs : list integer) ->
        case
          integer
          xs
          [ (\(x : integer) (xs : list integer) ->
               go (multiplyInteger acc x) xs)
          , acc ]
in
\(xs : list integer) -> go 1 xs
let
  !addInteger : integer -> integer -> integer = addInteger
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~length : all a. list a -> integer
    = /\a ->
        letrec
          ~go : list a -> integer
            = caseList'
                {a}
                {integer}
                0
                (\(x : a) (xs : list a) ->
                   let
                     !xs : list a = xs
                     !y : integer = go xs
                   in
                   addInteger 1 y)
        in
        go
in
\(xs : list integer) -> let !xs : list integer = xs in length {integer} xs
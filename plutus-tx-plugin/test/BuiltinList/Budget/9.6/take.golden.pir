letrec
  !take : all a. (\arep -> list arep) a -> integer -> list a -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) (n : integer) (l : list a) ->
          case
            (all dead. list a)
            (lessThanEqualsInteger n 0)
            [ (/\dead ->
                 (let
                     r = list a
                   in
                   \(z : r) (f : a -> list a -> r) (xs : list a) ->
                     case r xs [f, z])
                   `$dMkNil`
                   (\(x : a) (xs : list a) ->
                      mkCons
                        {a}
                        x
                        (take {a} `$dMkNil` (subtractInteger n 1) xs))
                   l)
            , (/\dead -> `$dMkNil`) ]
            {all dead. dead}
in
\(xs : list integer) -> take {integer} [] 5 xs
letrec
  !drop : all a. (\arep -> list arep) a -> integer -> list a -> list a
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
                   (\(ds : a) (xs : list a) ->
                      drop {a} `$dMkNil` (subtractInteger n 1) xs)
                   l)
            , (/\dead -> l) ]
            {all dead. dead}
in
\(xs : list integer) -> drop {integer} [] 5 xs
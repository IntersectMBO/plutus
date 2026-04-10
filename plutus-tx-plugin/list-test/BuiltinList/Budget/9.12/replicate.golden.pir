letrec
  !go : integer -> list integer
    = \(n : integer) ->
        case
          (all dead. list integer)
          (lessThanEqualsInteger n 0)
          [ (/\dead -> mkCons {integer} 0 (go (subtractInteger n 1)))
          , (/\dead -> []) ]
          {all dead. dead}
in
\(ds : list integer) -> go 10
letrec
  !go : list integer -> bool
    = \(xs : list integer) ->
        case
          bool
          xs
          [ (\(x : integer) (xs : list integer) ->
               case
                 (all dead. bool)
                 (lessThanEqualsInteger x 0)
                 [(/\dead -> go xs), (/\dead -> True)]
                 {all dead. dead})
          , False ]
in
\(xs : list integer) -> go xs
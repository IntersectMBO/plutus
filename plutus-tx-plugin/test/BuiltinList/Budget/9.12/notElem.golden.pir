letrec
  !go : list integer -> bool
    = \(xs : list integer) ->
        case
          bool
          xs
          [ (\(x : integer) (xs : list integer) ->
               case
                 (all dead. bool)
                 (equalsInteger 42 x)
                 [(/\dead -> go xs), (/\dead -> True)]
                 {all dead. dead})
          , False ]
in
\(xs : list integer) -> case bool (go xs) [True, False]
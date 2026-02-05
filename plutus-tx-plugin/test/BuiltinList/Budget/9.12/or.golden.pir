letrec
  !go : list bool -> bool
    = \(xs : list bool) ->
        case
          bool
          xs
          [ (\(x : bool) (xs : list bool) ->
               case
                 (all dead. bool)
                 (case bool x [False, True])
                 [(/\dead -> go xs), (/\dead -> True)]
                 {all dead. dead})
          , False ]
in
\(xs : list bool) -> go xs
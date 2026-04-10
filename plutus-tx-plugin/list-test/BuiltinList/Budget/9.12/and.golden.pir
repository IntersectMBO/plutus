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
                 [(/\dead -> False), (/\dead -> go xs)]
                 {all dead. dead})
          , True ]
in
\(xs : list bool) -> go xs
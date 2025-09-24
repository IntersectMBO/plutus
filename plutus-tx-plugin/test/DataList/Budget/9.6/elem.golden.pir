letrec
  !go : list data -> bool
    = \(xs : list data) ->
        case
          bool
          xs
          [ (\(h : data) (t : list data) ->
               case
                 (all dead. bool)
                 (equalsData (I 8) h)
                 [(/\dead -> go t), (/\dead -> True)]
                 {all dead. dead})
          , False ]
in
\(eta : (\a -> list data) integer) -> go eta
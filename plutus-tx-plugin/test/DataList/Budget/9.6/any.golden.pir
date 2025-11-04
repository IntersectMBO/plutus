letrec
  !go : (\a -> list data) integer -> bool
    = \(ds : (\a -> list data) integer) ->
        case
          bool
          ds
          [ (\(x : data) (eta : list data) ->
               case
                 (all dead. bool)
                 (case bool (lessThanInteger (unIData x) 8) [True, False])
                 [(/\dead -> go eta), (/\dead -> True)]
                 {all dead. dead})
          , False ]
in
\(eta : (\a -> list data) integer) -> go eta
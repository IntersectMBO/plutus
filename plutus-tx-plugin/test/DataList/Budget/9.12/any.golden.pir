letrec
  !go : (\a -> list data) integer -> bool
    = \(ds : (\a -> list data) integer) ->
        case
          bool
          ds
          [ (\(x : data) (eta : list data) ->
               case
                 (all dead. bool)
                 (lessThanEqualsInteger 8 (unIData x))
                 [(/\dead -> go eta), (/\dead -> True)]
                 {all dead. dead})
          , False ]
in
\(eta : (\a -> list data) integer) -> go eta
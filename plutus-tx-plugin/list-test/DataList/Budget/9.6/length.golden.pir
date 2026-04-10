letrec
  !go : list data -> integer
    = \(xs : list data) ->
        case
          integer
          xs
          [(\(ds : data) (eta : list data) -> addInteger 1 (go eta)), 0]
in
\(ds : (\a -> list data) integer) -> go ds
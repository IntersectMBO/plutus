letrec
  !go : (\a -> list data) integer -> (\a -> list data) integer
    = \(ds : (\a -> list data) integer) ->
        (let
            r = (\a -> list data) integer
          in
          \(z : r) (f : data -> list data -> r) (xs : list data) ->
            case r xs [f, z])
          []
          (\(x : data) (eta : list data) ->
             let
               !h : integer = unIData x
             in
             case
               (all dead. (\a -> list data) integer)
               (case bool (lessThanInteger h 8) [True, False])
               [ (/\dead -> go eta)
               , (/\dead ->
                    let
                      !nt : list data = go eta
                    in
                    mkCons {data} (iData h) nt) ]
               {all dead. dead})
          ds
in
\(eta : (\a -> list data) integer) -> go eta
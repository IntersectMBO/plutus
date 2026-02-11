\(xs : list integer) ->
  (let
      b = list integer
    in
    \(f : integer -> b -> b) (acc : b) ->
      letrec
        !go : list integer -> b
          = \(xs : list integer) ->
              case
                b
                xs
                [(\(x : integer) (xs : list integer) -> f x (go xs)), acc]
      in
      go)
    (mkCons {integer})
    xs
    xs
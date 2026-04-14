letrec
  !go : list (list integer) -> list integer
    = \(xs : list (list integer)) ->
        case
          (list integer)
          xs
          [ (\(x : list integer) (xs : list (list integer)) ->
               let
                 !r : list integer = go xs
               in
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
                             [ (\(x : integer) (xs : list integer) ->
                                  f x (go xs))
                             , acc ]
                   in
                   go)
                 (mkCons {integer})
                 r
                 x)
          , [] ]
in
\(xss : list (list integer)) -> go xss
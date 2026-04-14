letrec
  !go : list integer -> list integer
    = \(xs : list integer) ->
        case
          (list integer)
          xs
          [ (\(x : integer) ->
               letrec
                 !go : integer -> list integer
                   = \(n : integer) ->
                       case
                         (all dead. list integer)
                         (lessThanEqualsInteger n 0)
                         [ (/\dead ->
                              mkCons {integer} x (go (subtractInteger n 1)))
                         , (/\dead -> []) ]
                         {all dead. dead}
               in
               \(xs : list integer) ->
                 let
                   !ys : list integer = go xs
                   !l : list integer = go 2
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
                   ys
                   l)
          , [] ]
in
\(xss : list integer) -> go xss
letrec
  !go : list integer -> list integer -> list integer
    = \(l : list integer) (xs : list integer) ->
        case
          (list integer)
          l
          [ (\(y : integer) ->
               letrec
                 !go : list integer -> bool
                   = \(xs : list integer) ->
                       case
                         bool
                         xs
                         [ (\(x : integer) (xs : list integer) ->
                              case
                                (all dead. bool)
                                (lessThanEqualsInteger x y)
                                [(/\dead -> go xs), (/\dead -> True)]
                                {all dead. dead})
                         , False ]
               in
               \(ys : list integer) ->
                 case
                   (all dead. list integer)
                   (go xs)
                   [ (/\dead ->
                        mkCons {integer} y (go ys (mkCons {integer} y xs)))
                   , (/\dead -> go ys xs) ]
                   {all dead. dead})
          , [] ]
in
\(xs : list integer) -> go xs []
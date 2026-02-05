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
                                (equalsInteger x y)
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
\(xs : list integer) ->
  let
    !eta : list integer
      = (let
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
  in
  go eta []
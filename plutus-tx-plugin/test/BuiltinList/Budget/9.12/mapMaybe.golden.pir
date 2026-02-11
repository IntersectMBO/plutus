let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
\(xs : list integer) ->
  (letrec
      !go : list integer -> list integer
        = (let
              r = list integer
            in
            \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
              case r xs [f, z])
            []
            (\(x : integer) (xs : list integer) ->
               Maybe_match
                 {integer}
                 (case
                    (all dead. Maybe integer)
                    (case bool (equalsInteger 0 (modInteger x 2)) [True, False])
                    [ (/\dead -> Nothing {integer})
                    , (/\dead -> Just {integer} x) ]
                    {all dead. dead})
                 {all dead. list integer}
                 (\(y : integer) -> /\dead -> mkCons {integer} y (go xs))
                 (/\dead -> go xs)
                 {all dead. dead})
    in
    go)
    xs
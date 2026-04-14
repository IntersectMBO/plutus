let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
letrec
  !go : integer -> list integer -> Maybe integer
    = \(i : integer) ->
        (let
            r = Maybe integer
          in
          \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
            case r xs [f, z])
          (Nothing {integer})
          (\(x : integer) (xs : list integer) ->
             case
               (all dead. Maybe integer)
               (equalsInteger 4 x)
               [ (/\dead -> go (addInteger 1 i) xs)
               , (/\dead -> Just {integer} i) ]
               {all dead. dead})
in
\(xs : list integer) -> go 0 xs
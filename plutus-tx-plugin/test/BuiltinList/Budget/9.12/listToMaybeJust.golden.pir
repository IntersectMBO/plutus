let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
\(xs : list integer) ->
  (let
      r = Maybe integer
    in
    \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
      case r xs [f, z])
    (Nothing {integer})
    (\(x : integer) (ds : list integer) -> Just {integer} x)
    xs
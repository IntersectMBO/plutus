let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
\(ds : list integer) -> Nothing {integer}
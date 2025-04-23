let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
\(ds : (\a -> Maybe a) integer) ->
  let
    !nt : Maybe integer = ds
  in
  Maybe_match {integer} nt {integer} (\(i : integer) -> i) 1
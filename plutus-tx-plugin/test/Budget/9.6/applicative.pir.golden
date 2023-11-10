let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !ds : Maybe (integer -> integer)
    = (let
          b = integer -> integer
        in
        \(f : integer -> b) (ds : Maybe integer) ->
          Maybe_match
            {integer}
            ds
            {all dead. Maybe b}
            (\(a : integer) -> /\dead -> Just {b} (f a))
            (/\dead -> Nothing {b})
            {all dead. dead})
        (\(x : integer) (y : integer) -> addInteger x y)
        (Just {integer} 1)
in
Maybe_match
  {integer -> integer}
  ds
  {all dead. Maybe integer}
  (\(ipv : integer -> integer) -> /\dead -> Just {integer} (ipv 2))
  (/\dead -> Nothing {integer})
  {all dead. dead}
let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !`$fMonadMaybe_$c>>=` : all a b. Maybe a -> (a -> Maybe b) -> Maybe b
    = /\a b ->
        \(ds : Maybe a) (k : a -> Maybe b) ->
          Maybe_match
            {a}
            ds
            {all dead. Maybe b}
            (\(x : a) -> /\dead -> k x)
            (/\dead -> Nothing {b})
            {all dead. dead}
in
`$fMonadMaybe_$c>>=`
  {integer}
  {integer}
  (Just {integer} 1)
  (\(x' : integer) ->
     `$fMonadMaybe_$c>>=`
       {integer}
       {integer}
       (Just {integer} 2)
       (\(y' : integer) -> Just {integer} (addInteger x' y')))
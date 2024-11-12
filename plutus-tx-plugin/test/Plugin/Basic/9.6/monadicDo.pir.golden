let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  ~`$fApplicativeMaybe_$cpure` : all a. a -> Maybe a
    = /\a -> \(ds : a) -> Just {a} ds
  ~`$fMonadMaybe_$c>>=` : all a b. Maybe a -> (a -> Maybe b) -> Maybe b
    = /\a b ->
        \(ds : Maybe a) (k : a -> Maybe b) ->
          Maybe_match
            {a}
            ds
            {all dead. Maybe b}
            (\(x : a) -> /\dead -> k x)
            (/\dead -> Nothing {b})
            {all dead. dead}
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
in
\(ds : Maybe integer) ->
  let
    !ds : Maybe integer = ds
  in
  \(ds : Maybe integer) ->
    let
      !ds : Maybe integer = ds
    in
    `$fMonadMaybe_$c>>=`
      {integer}
      {integer}
      ds
      (\(x' : integer) ->
         let
           !x' : integer = x'
         in
         `$fMonadMaybe_$c>>=`
           {integer}
           {integer}
           ds
           (\(y' : integer) ->
              let
                !y' : integer = y'
              in
              `$fApplicativeMaybe_$cpure` {integer} (addInteger x' y')))
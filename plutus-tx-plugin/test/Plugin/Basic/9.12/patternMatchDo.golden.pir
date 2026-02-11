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
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
in
\(ds : Maybe (Tuple integer integer)) ->
  let
    !ds : Maybe (Tuple integer integer) = ds
  in
  \(ds : Maybe integer) ->
    let
      !ds : Maybe integer = ds
    in
    `$fMonadMaybe_$c>>=`
      {Tuple integer integer}
      {integer}
      ds
      (\(ds : Tuple integer integer) ->
         Tuple_match
           {integer}
           {integer}
           ds
           {Maybe integer}
           (\(x : integer) (x : integer) ->
              `$fMonadMaybe_$c>>=`
                {integer}
                {integer}
                ds
                (\(y' : integer) ->
                   let
                     !y' : integer = y'
                   in
                   `$fApplicativeMaybe_$cpure`
                     {integer}
                     (addInteger (addInteger x x) y'))))
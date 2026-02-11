let
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
\(t : Tuple integer integer) ->
  Tuple_match
    {integer}
    {integer}
    t
    {integer}
    (\(ds : integer) (ds : integer) -> addInteger ds ds)
let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
in
\(t : Tuple2 integer integer) ->
  Tuple2_match
    {integer}
    {integer}
    t
    {integer}
    (\(ds : integer) (ds : integer) -> addInteger ds ds)
let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
\(ds : Tuple2 integer integer) ->
  Tuple2_match
    {integer}
    {integer}
    ds
    {integer}
    (\(ipv : integer) (ipv : integer) -> ipv)
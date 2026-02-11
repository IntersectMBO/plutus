let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
in
\(ds : Tuple integer integer) ->
  Tuple_match
    {integer}
    {integer}
    ds
    {integer}
    (\(ipv : integer) (ipv : integer) -> ipv)
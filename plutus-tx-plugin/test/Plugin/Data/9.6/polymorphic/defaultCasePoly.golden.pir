let
  data (MyPolyData :: * -> * -> *) a b | MyPolyData_match where
    Poly : a -> b -> MyPolyData a b
    Poly : a -> MyPolyData a b
in
\(ds : MyPolyData integer integer) ->
  let
    !ds : MyPolyData integer integer = ds
  in
  MyPolyData_match
    {integer}
    {integer}
    ds
    {integer}
    (\(a : integer) (ds : integer) -> a)
    (\(ipv : integer) -> 2)
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
    (\(ipv : integer) (ipv : integer) -> 1)
    (\(i : integer) -> i)
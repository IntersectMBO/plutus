let
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
in
\(ds : integer) ->
  let
    !ds : integer = ds
  in
  \(ds : integer) -> let !ds : integer = ds in equalsInteger ds ds
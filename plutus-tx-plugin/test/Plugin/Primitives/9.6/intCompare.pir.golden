let
  !lessThanInteger : integer -> integer -> bool = lessThanInteger
  ~lessThanInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in lessThanInteger x y
in
\(ds : integer) ->
  let
    !ds : integer = ds
  in
  \(ds : integer) -> let !ds : integer = ds in lessThanInteger ds ds
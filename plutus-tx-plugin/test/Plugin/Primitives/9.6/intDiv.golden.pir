let
  !divideInteger : integer -> integer -> integer = divideInteger
  ~divideInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in divideInteger x y
in
\(ds : integer) ->
  let
    !ds : integer = ds
  in
  \(ds : integer) -> let !ds : integer = ds in divideInteger ds ds
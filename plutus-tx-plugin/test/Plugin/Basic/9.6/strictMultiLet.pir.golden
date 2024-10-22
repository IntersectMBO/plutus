let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
in
\(ds : integer) ->
  let
    !ds : integer = ds
  in
  \(ds : integer) ->
    let
      !ds : integer = ds
      !z : integer = addInteger ds ds
      !q : integer = addInteger z z
    in
    addInteger q q
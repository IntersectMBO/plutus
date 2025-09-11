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
    in
    letrec
      ~q : integer = addInteger ds z
      ~z : integer = addInteger ds q
    in
    let
      !z : integer = z
      !q : integer = q
    in
    addInteger z z
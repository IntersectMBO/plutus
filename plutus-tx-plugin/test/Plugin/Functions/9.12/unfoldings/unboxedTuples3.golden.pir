let
  data (`Tuple3#` :: * -> * -> * -> *) a b c | `Tuple3#_match` where
    UTuple3 : a -> b -> c -> `Tuple3#` a b c
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~unboxedTuple : `Tuple3#` integer integer integer -> integer
    = \(ds : `Tuple3#` integer integer integer) ->
        `Tuple3#_match`
          {integer}
          {integer}
          {integer}
          ds
          {integer}
          (\(i : integer) (j : integer) (k : integer) ->
             addInteger (addInteger i j) k)
in
\(x : integer) ->
  let
    !x : integer = x
  in
  unboxedTuple (UTuple3 {integer} {integer} {integer} x x x)
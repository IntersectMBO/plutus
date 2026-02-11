let
  data (`Tuple4#` :: * -> * -> * -> * -> *) a b c d | `Tuple4#_match` where
    UTuple4 : a -> b -> c -> d -> `Tuple4#` a b c d
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~unboxedTuple : `Tuple4#` integer integer integer integer -> integer
    = \(ds : `Tuple4#` integer integer integer integer) ->
        `Tuple4#_match`
          {integer}
          {integer}
          {integer}
          {integer}
          ds
          {integer}
          (\(i : integer) (j : integer) (k : integer) (l : integer) ->
             addInteger (addInteger (addInteger i j) k) l)
in
\(x : integer) ->
  let
    !x : integer = x
  in
  unboxedTuple (UTuple4 {integer} {integer} {integer} {integer} x x x x)
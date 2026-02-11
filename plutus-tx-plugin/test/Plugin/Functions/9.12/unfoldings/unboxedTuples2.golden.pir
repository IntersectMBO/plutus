let
  data (`Tuple2#` :: * -> * -> *) a b | `Tuple2#_match` where
    UTuple2 : a -> b -> `Tuple2#` a b
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~unboxedTuple : `Tuple2#` integer integer -> integer
    = \(ds : `Tuple2#` integer integer) ->
        `Tuple2#_match`
          {integer}
          {integer}
          ds
          {integer}
          (\(i : integer) (j : integer) -> addInteger i j)
in
\(x : integer) ->
  let
    !x : integer = x
  in
  unboxedTuple (UTuple2 {integer} {integer} x x)
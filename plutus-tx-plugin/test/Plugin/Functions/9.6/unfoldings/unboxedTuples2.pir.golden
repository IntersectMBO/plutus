let
  data (UTuple2 :: * -> * -> *) a b | UTuple2_match where
    UTuple2 : a -> b -> UTuple2 a b
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~unboxedTuple : UTuple2 integer integer -> integer
    = \(ds : UTuple2 integer integer) ->
        UTuple2_match
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
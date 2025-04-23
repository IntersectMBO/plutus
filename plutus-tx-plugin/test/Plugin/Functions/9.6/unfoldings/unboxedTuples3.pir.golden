let
  data (UTuple3 :: * -> * -> * -> *) a b c | UTuple3_match where
    UTuple3 : a -> b -> c -> UTuple3 a b c
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~unboxedTuple : UTuple3 integer integer integer -> integer
    = \(ds : UTuple3 integer integer integer) ->
        UTuple3_match
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
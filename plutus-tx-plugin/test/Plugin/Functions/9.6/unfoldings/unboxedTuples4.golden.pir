let
  data (UTuple4 :: * -> * -> * -> * -> *) a b c d | UTuple4_match where
    UTuple4 : a -> b -> c -> d -> UTuple4 a b c d
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~unboxedTuple : UTuple4 integer integer integer integer -> integer
    = \(ds : UTuple4 integer integer integer integer) ->
        UTuple4_match
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
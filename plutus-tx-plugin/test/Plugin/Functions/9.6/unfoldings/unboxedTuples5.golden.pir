let
  data (UTuple5 :: * -> * -> * -> * -> * -> *) a b c d e | UTuple5_match where
    UTuple5 : a -> b -> c -> d -> e -> UTuple5 a b c d e
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~unboxedTuple : UTuple5 integer integer integer integer integer -> integer
    = \(ds : UTuple5 integer integer integer integer integer) ->
        UTuple5_match
          {integer}
          {integer}
          {integer}
          {integer}
          {integer}
          ds
          {integer}
          (\(i : integer)
            (j : integer)
            (k : integer)
            (l : integer)
            (m : integer) ->
             addInteger (addInteger (addInteger (addInteger i j) k) l) m)
in
\(x : integer) ->
  let
    !x : integer = x
  in
  unboxedTuple
    (UTuple5 {integer} {integer} {integer} {integer} {integer} x x x x x)
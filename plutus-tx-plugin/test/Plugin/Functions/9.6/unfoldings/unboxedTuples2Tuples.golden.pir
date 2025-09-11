let
  data (UTuple2 :: * -> * -> *) a b | UTuple2_match where
    UTuple2 : a -> b -> UTuple2 a b
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
  ~unboxedTuples2Tuple :
     UTuple2
       (UTuple5 integer integer integer integer integer)
       (UTuple5 integer integer integer integer integer) ->
     integer
    = \(ds :
          UTuple2
            (UTuple5 integer integer integer integer integer)
            (UTuple5 integer integer integer integer integer)) ->
        UTuple2_match
          {UTuple5 integer integer integer integer integer}
          {UTuple5 integer integer integer integer integer}
          ds
          {integer}
          (\(i : UTuple5 integer integer integer integer integer)
            (j : UTuple5 integer integer integer integer integer) ->
             addInteger (unboxedTuple i) (unboxedTuple j))
in
\(x : integer) ->
  let
    !x : integer = x
  in
  unboxedTuples2Tuple
    (UTuple2
       {UTuple5 integer integer integer integer integer}
       {UTuple5 integer integer integer integer integer}
       (UTuple5 {integer} {integer} {integer} {integer} {integer} x x x x x)
       (UTuple5 {integer} {integer} {integer} {integer} {integer} x x x x x))
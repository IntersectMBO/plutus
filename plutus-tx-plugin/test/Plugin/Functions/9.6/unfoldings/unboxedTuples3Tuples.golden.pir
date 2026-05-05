let
  data (UTuple3 :: * -> * -> * -> *) a b c | UTuple3_match where
    UTuple3 : a -> b -> c -> UTuple3 a b c
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
          (\(i : integer) (j : integer) (k : integer) ->
             let
               !y : integer = k
             in
             \(l : integer) ->
               let
                 !y : integer = l
               in
               \(m : integer) ->
                 let
                   !y : integer = m
                   !x : integer
                     = let
                       !x : integer
                         = let
                           !x : integer = addInteger i j
                         in
                         addInteger x y
                     in
                     addInteger x y
                 in
                 addInteger x y)
  ~unboxedTuples3Tuple :
     UTuple3
       (UTuple5 integer integer integer integer integer)
       (UTuple5 integer integer integer integer integer)
       (UTuple5 integer integer integer integer integer) ->
     integer
    = \(ds :
          UTuple3
            (UTuple5 integer integer integer integer integer)
            (UTuple5 integer integer integer integer integer)
            (UTuple5 integer integer integer integer integer)) ->
        UTuple3_match
          {UTuple5 integer integer integer integer integer}
          {UTuple5 integer integer integer integer integer}
          {UTuple5 integer integer integer integer integer}
          ds
          {integer}
          (\(i : UTuple5 integer integer integer integer integer)
            (j : UTuple5 integer integer integer integer integer)
            (k : UTuple5 integer integer integer integer integer) ->
             let
               !x : integer
                 = let
                   !x : integer = unboxedTuple i
                   !y : integer = unboxedTuple j
                 in
                 addInteger x y
               !y : integer = unboxedTuple k
             in
             addInteger x y)
in
\(x : integer) ->
  let
    !x : integer = x
  in
  unboxedTuples3Tuple
    (UTuple3
       {UTuple5 integer integer integer integer integer}
       {UTuple5 integer integer integer integer integer}
       {UTuple5 integer integer integer integer integer}
       (UTuple5 {integer} {integer} {integer} {integer} {integer} x x x x x)
       (UTuple5 {integer} {integer} {integer} {integer} {integer} x x x x x)
       (UTuple5 {integer} {integer} {integer} {integer} {integer} x x x x x))
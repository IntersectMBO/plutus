let
  data (`Tuple2#` :: * -> * -> *) a b | `Tuple2#_match` where
    UTuple2 : a -> b -> `Tuple2#` a b
  data (`Tuple5#` :: * -> * -> * -> * -> * -> *) a b c d
  e | `Tuple5#_match` where
    UTuple5 : a -> b -> c -> d -> e -> `Tuple5#` a b c d e
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~unboxedTuple : `Tuple5#` integer integer integer integer integer -> integer
    = \(ds : `Tuple5#` integer integer integer integer integer) ->
        `Tuple5#_match`
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
     `Tuple2#`
       (`Tuple5#` integer integer integer integer integer)
       (`Tuple5#` integer integer integer integer integer) ->
     integer
    = \(ds :
          `Tuple2#`
            (`Tuple5#` integer integer integer integer integer)
            (`Tuple5#` integer integer integer integer integer)) ->
        `Tuple2#_match`
          {`Tuple5#` integer integer integer integer integer}
          {`Tuple5#` integer integer integer integer integer}
          ds
          {integer}
          (\(i : `Tuple5#` integer integer integer integer integer)
            (j : `Tuple5#` integer integer integer integer integer) ->
             addInteger (unboxedTuple i) (unboxedTuple j))
in
\(x : integer) ->
  let
    !x : integer = x
  in
  unboxedTuples2Tuple
    (UTuple2
       {`Tuple5#` integer integer integer integer integer}
       {`Tuple5#` integer integer integer integer integer}
       (UTuple5 {integer} {integer} {integer} {integer} {integer} x x x x x)
       (UTuple5 {integer} {integer} {integer} {integer} {integer} x x x x x))
let
  Tuple2 :: * -> * -> * = \a a -> all a. a -> a
in
letrec
  data (B :: * -> *) a | B_match where
    One : a -> B a
    Two : B (Tuple2 a a) -> B a
in
\(ds : B integer) ->
  let
    !ds : B integer = ds
  in
  B_match
    {integer}
    ds
    {integer}
    (\(a : integer) -> a)
    (\(ds : B (Tuple2 integer integer)) -> 2)
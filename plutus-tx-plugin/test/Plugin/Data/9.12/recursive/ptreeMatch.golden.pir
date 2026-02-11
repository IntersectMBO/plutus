let
  Tuple :: * -> * -> * = \a a -> all a. a -> a
in
letrec
  data (B :: * -> *) a | B_match where
    One : a -> B a
    Two : B (Tuple a a) -> B a
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
    (\(ds : B (Tuple integer integer)) -> 2)
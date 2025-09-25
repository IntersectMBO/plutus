let
  ~v : integer = 12
  ~v : integer = 8
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~find : all a. (a -> bool) -> list a -> Maybe a
    = /\a ->
        \(p : a -> bool) ->
          let
            !p : a -> bool = p
          in
          letrec
            ~go : list a -> Maybe a
              = caseList'
                  {a}
                  {Maybe a}
                  (Nothing {a})
                  (\(x : a) ->
                     let
                       !x : a = x
                     in
                     \(xs : list a) ->
                       let
                         !xs : list a = xs
                       in
                       case
                         (all dead. Maybe a)
                         (p x)
                         [(/\dead -> go xs), (/\dead -> Just {a} x)]
                         {all dead. dead})
          in
          go
  !ifThenElse : all a. bool -> a -> a -> a
    = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
  !lessThanInteger : integer -> integer -> bool = lessThanInteger
  ~greaterThanEqualsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) ->
          let
            !y : integer = y
          in
          ifThenElse {bool} (lessThanInteger x y) False True
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  Tuple2
    {Maybe integer}
    {Maybe integer}
    (find {integer} (\(v : integer) -> greaterThanEqualsInteger v v) xs)
    (find {integer} (\(v : integer) -> greaterThanEqualsInteger v v) xs)
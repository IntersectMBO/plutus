let
  ~v : integer = 12
  ~v : integer = 8
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~any : all a. (a -> bool) -> list a -> bool
    = /\a ->
        \(p : a -> bool) ->
          let
            !p : a -> bool = p
          in
          letrec
            ~go : list a -> bool
              = caseList'
                  {a}
                  {bool}
                  False
                  (\(x : a) ->
                     let
                       !x : a = x
                     in
                     \(xs : list a) ->
                       let
                         !xs : list a = xs
                       in
                       case
                         (all dead. bool)
                         (p x)
                         [(/\dead -> go xs), (/\dead -> True)]
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
    {bool}
    {bool}
    (any {integer} (\(v : integer) -> greaterThanEqualsInteger v v) xs)
    (any {integer} (\(v : integer) -> greaterThanEqualsInteger v v) xs)
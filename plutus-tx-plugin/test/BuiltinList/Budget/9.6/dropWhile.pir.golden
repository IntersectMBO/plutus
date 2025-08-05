let
  ~v : integer = 5
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~dropWhile : all a. (a -> bool) -> list a -> list a
    = /\a ->
        \(p : a -> bool) ->
          let
            !p : a -> bool = p
          in
          letrec
            ~go : list a -> list a
              = \(xs : list a) ->
                  let
                    !xs : list a = xs
                  in
                  caseList'
                    {a}
                    {list a}
                    xs
                    (\(x : a) ->
                       let
                         !x : a = x
                       in
                       \(xs' : list a) ->
                         let
                           !xs' : list a = xs'
                         in
                         case
                           (all dead. list a)
                           (p x)
                           [(/\dead -> xs), (/\dead -> go xs')]
                           {all dead. dead})
                    xs
          in
          \(eta : list a) -> go eta
  !lessThanInteger : integer -> integer -> bool = lessThanInteger
  ~lessThanInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in lessThanInteger x y
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  dropWhile {integer} (\(v : integer) -> lessThanInteger v v) xs
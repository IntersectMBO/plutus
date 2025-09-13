let
  ~v : integer = 99
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  ~`$fEqInteger` : (\a -> a -> a -> bool) integer = equalsInteger
  ~`==` : all a. (\a -> a -> a -> bool) a -> a -> a -> bool
    = /\a -> \(v : (\a -> a -> a -> bool) a) -> v
  ~v : integer -> integer -> bool = `==` {integer} `$fEqInteger`
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !addInteger : integer -> integer -> integer = addInteger
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~findIndex : all a. (a -> bool) -> list a -> Maybe integer
    = /\a ->
        \(f : a -> bool) ->
          let
            !f : a -> bool = f
          in
          letrec
            ~go : integer -> list a -> Maybe integer
              = \(i : integer) ->
                  let
                    !i : integer = i
                  in
                  caseList'
                    {a}
                    {Maybe integer}
                    (Nothing {integer})
                    (\(x : a) ->
                       let
                         !x : a = x
                       in
                       \(xs : list a) ->
                         let
                           !xs : list a = xs
                         in
                         case
                           (all dead. Maybe integer)
                           (f x)
                           [ (/\dead -> go (addInteger i 1) xs)
                           , (/\dead -> Just {integer} i) ]
                           {all dead. dead})
          in
          go 0
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  findIndex {integer} (\(v : integer) -> v v v) xs
let
  data (AdditiveMonoid :: * -> *) a | AdditiveMonoid_match where
    CConsAdditiveMonoid : (\a -> a -> a -> a) a -> a -> AdditiveMonoid a
  !`$dAdditiveMonoid` : AdditiveMonoid integer
    = CConsAdditiveMonoid
        {integer}
        (\(x : integer) (y : integer) -> addInteger x y)
        0
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  !ls : List integer
    = (let
          a = List integer
        in
        \(c : integer -> a -> a) (n : a) ->
          c 1 (c 2 (c 3 (c 4 (c 5 (c 6 (c 7 (c 8 (c 9 (c 10 n))))))))))
        (\(ds : integer) (ds : List integer) -> Cons {integer} ds ds)
        (Nil {integer})
in
(let
    !f : integer -> integer -> integer
      = AdditiveMonoid_match
          {integer}
          `$dAdditiveMonoid`
          {(\a -> a -> a -> a) integer}
          (\(v : (\a -> a -> a -> a) integer) (v : integer) -> v)
    !z : integer
      = AdditiveMonoid_match
          {integer}
          `$dAdditiveMonoid`
          {integer}
          (\(v : (\a -> a -> a -> a) integer) (v : integer) -> v)
  in
  letrec
    !go : List integer -> integer
      = \(ds : List integer) ->
          List_match
            {integer}
            ds
            {all dead. integer}
            (/\dead -> z)
            (\(x : integer) (xs : List integer) -> /\dead -> f x (go xs))
            {all dead. dead}
  in
  \(eta : List integer) -> go eta)
  ls
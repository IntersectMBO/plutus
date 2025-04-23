letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
in
letrec
  ~sum : List integer -> integer
    = \(ds : List integer) ->
        List_match
          {integer}
          ds
          {integer}
          0
          (\(x : integer) (xs : List integer) -> addInteger x (sum xs))
in
sum
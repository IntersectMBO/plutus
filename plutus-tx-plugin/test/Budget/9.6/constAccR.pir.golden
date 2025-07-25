letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !go : List integer -> integer
    = \(ds : List integer) ->
        List_match
          {integer}
          ds
          {all dead. integer}
          (/\dead -> 42)
          (\(x : integer) (xs : List integer) -> /\dead -> go xs)
          {all dead. dead}
in
letrec
  !go : integer -> List integer
    = \(n : integer) ->
        case
          (all dead. List integer)
          (lessThanEqualsInteger n 0)
          [ (/\dead -> Cons {integer} 1 (go (subtractInteger n 1)))
          , (/\dead -> Nil {integer}) ]
          {all dead. dead}
in
let
  !ls : List integer = go 1000
in
go ls
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !go : List integer -> bool
    = \(ds : List integer) ->
        List_match
          {integer}
          ds
          {bool}
          True
          (\(x : integer) (xs : List integer) ->
             case
               (all dead. bool)
               (case bool (lessThanInteger x 0) [True, False])
               [(/\dead -> False), (/\dead -> go xs)]
               {all dead. dead})
in
letrec
  !go : integer -> List integer
    = \(n : integer) ->
        case
          (all dead. List integer)
          (lessThanEqualsInteger n 0)
          [ (/\dead -> Cons {integer} 0 (go (subtractInteger n 1)))
          , (/\dead -> Nil {integer}) ]
          {all dead. dead}
in
let
  !ls : List integer = go 1000
in
go ls
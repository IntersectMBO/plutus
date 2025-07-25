letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
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
letrec
  !recursiveAll : all a. (a -> bool) -> List a -> bool
    = /\a ->
        \(ds : a -> bool) (ds : List a) ->
          List_match
            {a}
            ds
            {bool}
            True
            (\(x : a) (xs : List a) ->
               case
                 (all dead. bool)
                 (ds x)
                 [(/\dead -> False), (/\dead -> recursiveAll {a} ds xs)]
                 {all dead. dead})
in
let
  !ls : List integer = go 1000
in
recursiveAll
  {integer}
  (\(v : integer) -> case bool (lessThanInteger v 0) [True, False])
  ls
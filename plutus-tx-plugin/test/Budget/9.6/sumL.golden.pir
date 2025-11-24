letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !go : integer -> List integer -> integer
    = \(acc : integer) (ds : List integer) ->
        List_match
          {integer}
          ds
          {all dead. integer}
          (/\dead -> acc)
          (\(x : integer) (xs : List integer) ->
             /\dead -> go (addInteger acc x) xs)
          {all dead. dead}
in
letrec
  !`$dmenumFromTo_$cenumFromTo` : integer -> integer -> List integer
    = \(x : integer) (lim : integer) ->
        case
          (all dead. List integer)
          (case bool (lessThanEqualsInteger x lim) [True, False])
          [ (/\dead ->
               Cons
                 {integer}
                 x
                 (`$dmenumFromTo_$cenumFromTo` (addInteger 1 x) lim))
          , (/\dead -> Nil {integer}) ]
          {all dead. dead}
in
let
  !ls : List integer = `$dmenumFromTo_$cenumFromTo` 1 1000
in
go 0 ls
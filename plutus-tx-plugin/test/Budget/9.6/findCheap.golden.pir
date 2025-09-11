letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
letrec
  !go : List integer -> Maybe integer
    = \(ds : List integer) ->
        List_match
          {integer}
          ds
          {all dead. Maybe integer}
          (/\dead -> Nothing {integer})
          (\(x : integer) (xs : List integer) ->
             /\dead ->
               case
                 (all dead. Maybe integer)
                 (case bool (lessThanEqualsInteger 10 x) [True, False])
                 [(/\dead -> go xs), (/\dead -> Just {integer} x)]
                 {all dead. dead})
          {all dead. dead}
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
go ls
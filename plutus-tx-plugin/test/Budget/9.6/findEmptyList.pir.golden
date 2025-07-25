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
                 (case bool (lessThanEqualsInteger 1 x) [True, False])
                 [(/\dead -> go xs), (/\dead -> Just {integer} x)]
                 {all dead. dead})
          {all dead. dead}
in
go (Nil {integer})
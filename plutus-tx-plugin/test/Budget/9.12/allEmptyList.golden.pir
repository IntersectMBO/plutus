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
               (lessThanInteger x 1)
               [(/\dead -> False), (/\dead -> go xs)]
               {all dead. dead})
in
go (Nil {integer})
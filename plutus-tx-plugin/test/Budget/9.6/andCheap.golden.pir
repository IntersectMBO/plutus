letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !and : List bool -> bool
    = \(ds : List bool) ->
        List_match
          {bool}
          ds
          {bool}
          True
          (\(x : bool) (xs : List bool) ->
             case (all dead. bool) x [(/\dead -> False), (/\dead -> and xs)]
               {all dead. dead})
in
and
  ((let
       a = List bool
     in
     \(c : bool -> a -> a) (n : a) ->
       c
         False
         (c
            True
            (c
               True
               (c
                  True
                  (c True (c True (c True (c True (c True (c True n))))))))))
     (\(ds : bool) (ds : List bool) -> Cons {bool} ds ds)
     (Nil {bool}))
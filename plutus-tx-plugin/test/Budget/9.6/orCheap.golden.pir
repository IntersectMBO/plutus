letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !or : List bool -> bool
    = \(ds : List bool) ->
        List_match
          {bool}
          ds
          {bool}
          False
          (\(x : bool) (xs : List bool) ->
             case (all dead. bool) x [(/\dead -> or xs), (/\dead -> True)]
               {all dead. dead})
in
or
  ((let
       a = List bool
     in
     \(c : bool -> a -> a) (n : a) ->
       c
         True
         (c
            False
            (c
               False
               (c
                  False
                  (c
                     False
                     (c False (c False (c False (c False (c False n))))))))))
     (\(ds : bool) (ds : List bool) -> Cons {bool} ds ds)
     (Nil {bool}))
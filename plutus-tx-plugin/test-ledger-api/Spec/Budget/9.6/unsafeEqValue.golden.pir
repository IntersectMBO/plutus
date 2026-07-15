let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !goInner :
     List (Tuple2 bytestring integer) ->
     List (Tuple2 bytestring integer) ->
     bool
    = \(ds : List (Tuple2 bytestring integer))
       (ds : List (Tuple2 bytestring integer)) ->
        List_match
          {Tuple2 bytestring integer}
          ds
          {all dead. bool}
          (/\dead ->
             List_match
               {Tuple2 bytestring integer}
               ds
               {bool}
               True
               (\(ipv : Tuple2 bytestring integer)
                 (ipv : List (Tuple2 bytestring integer)) ->
                  False))
          (\(ds : Tuple2 bytestring integer)
            (rest : List (Tuple2 bytestring integer)) ->
             /\dead ->
               Tuple2_match
                 {bytestring}
                 {integer}
                 ds
                 {bool}
                 (\(t : bytestring) (q : integer) ->
                    List_match
                      {Tuple2 bytestring integer}
                      ds
                      {bool}
                      False
                      (\(ds : Tuple2 bytestring integer)
                        (rest : List (Tuple2 bytestring integer)) ->
                         Tuple2_match
                           {bytestring}
                           {integer}
                           ds
                           {bool}
                           (\(t : bytestring) (q : integer) ->
                              case
                                (all dead. bool)
                                (equalsByteString t t)
                                [ (/\dead -> False)
                                , (/\dead ->
                                     case
                                       (all dead. bool)
                                       (equalsInteger q q)
                                       [ (/\dead -> False)
                                       , (/\dead -> goInner rest rest) ]
                                       {all dead. dead}) ]
                                {all dead. dead}))))
          {all dead. dead}
in
letrec
  !goOuter :
     List
       (Tuple2 bytestring ((\k v -> List (Tuple2 k v)) bytestring integer)) ->
     List
       (Tuple2 bytestring ((\k v -> List (Tuple2 k v)) bytestring integer)) ->
     bool
    = \(ds :
          List
            (Tuple2
               bytestring
               ((\k v -> List (Tuple2 k v)) bytestring integer)))
       (ds :
          List
            (Tuple2
               bytestring
               ((\k v -> List (Tuple2 k v)) bytestring integer))) ->
        List_match
          {Tuple2 bytestring ((\k v -> List (Tuple2 k v)) bytestring integer)}
          ds
          {all dead. bool}
          (/\dead ->
             List_match
               {Tuple2
                  bytestring
                  ((\k v -> List (Tuple2 k v)) bytestring integer)}
               ds
               {bool}
               True
               (\(ipv :
                    Tuple2
                      bytestring
                      ((\k v -> List (Tuple2 k v)) bytestring integer))
                 (ipv :
                    List
                      (Tuple2
                         bytestring
                         ((\k v -> List (Tuple2 k v)) bytestring integer))) ->
                  False))
          (\(ds :
               Tuple2
                 bytestring
                 ((\k v -> List (Tuple2 k v)) bytestring integer))
            (rest :
               List
                 (Tuple2
                    bytestring
                    ((\k v -> List (Tuple2 k v)) bytestring integer))) ->
             /\dead ->
               Tuple2_match
                 {bytestring}
                 {(\k v -> List (Tuple2 k v)) bytestring integer}
                 ds
                 {bool}
                 (\(c : bytestring)
                   (tokens : (\k v -> List (Tuple2 k v)) bytestring integer) ->
                    List_match
                      {Tuple2
                         bytestring
                         ((\k v -> List (Tuple2 k v)) bytestring integer)}
                      ds
                      {bool}
                      False
                      (\(ds :
                           Tuple2
                             bytestring
                             ((\k v -> List (Tuple2 k v)) bytestring integer))
                        (rest :
                           List
                             (Tuple2
                                bytestring
                                ((\k v -> List (Tuple2 k v))
                                   bytestring
                                   integer))) ->
                         Tuple2_match
                           {bytestring}
                           {(\k v -> List (Tuple2 k v)) bytestring integer}
                           ds
                           {bool}
                           (\(c : bytestring)
                             (tokens :
                                (\k v -> List (Tuple2 k v))
                                  bytestring
                                  integer) ->
                              case
                                (all dead. bool)
                                (equalsByteString c c)
                                [ (/\dead -> False)
                                , (/\dead ->
                                     case
                                       (all dead. bool)
                                       (goInner tokens tokens)
                                       [ (/\dead -> False)
                                       , (/\dead -> goOuter rest rest) ]
                                       {all dead. dead}) ]
                                {all dead. dead}))))
          {all dead. dead}
in
\(ds :
    (\k v -> List (Tuple2 k v))
      bytestring
      ((\k v -> List (Tuple2 k v)) bytestring integer))
 (ds :
    (\k v -> List (Tuple2 k v))
      bytestring
      ((\k v -> List (Tuple2 k v)) bytestring integer)) ->
  goOuter ds ds
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
in
letrec
  !goInner :
     List (Tuple bytestring integer) -> List (Tuple bytestring integer) -> bool
    = \(ds : List (Tuple bytestring integer))
       (ds : List (Tuple bytestring integer)) ->
        List_match
          {Tuple bytestring integer}
          ds
          {all dead. bool}
          (/\dead ->
             List_match
               {Tuple bytestring integer}
               ds
               {bool}
               True
               (\(ipv : Tuple bytestring integer)
                 (ipv : List (Tuple bytestring integer)) ->
                  False))
          (\(ds : Tuple bytestring integer)
            (rest : List (Tuple bytestring integer)) ->
             /\dead ->
               Tuple_match
                 {bytestring}
                 {integer}
                 ds
                 {bool}
                 (\(t : bytestring) (q : integer) ->
                    List_match
                      {Tuple bytestring integer}
                      ds
                      {bool}
                      False
                      (\(ds : Tuple bytestring integer)
                        (rest : List (Tuple bytestring integer)) ->
                         Tuple_match
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
     List (Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer)) ->
     List (Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer)) ->
     bool
    = \(ds :
          List
            (Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer)))
       (ds :
          List
            (Tuple
               bytestring
               ((\k v -> List (Tuple k v)) bytestring integer))) ->
        List_match
          {Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer)}
          ds
          {all dead. bool}
          (/\dead ->
             List_match
               {Tuple
                  bytestring
                  ((\k v -> List (Tuple k v)) bytestring integer)}
               ds
               {bool}
               True
               (\(ipv :
                    Tuple
                      bytestring
                      ((\k v -> List (Tuple k v)) bytestring integer))
                 (ipv :
                    List
                      (Tuple
                         bytestring
                         ((\k v -> List (Tuple k v)) bytestring integer))) ->
                  False))
          (\(ds :
               Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer))
            (rest :
               List
                 (Tuple
                    bytestring
                    ((\k v -> List (Tuple k v)) bytestring integer))) ->
             /\dead ->
               Tuple_match
                 {bytestring}
                 {(\k v -> List (Tuple k v)) bytestring integer}
                 ds
                 {bool}
                 (\(c : bytestring)
                   (tokens : (\k v -> List (Tuple k v)) bytestring integer) ->
                    List_match
                      {Tuple
                         bytestring
                         ((\k v -> List (Tuple k v)) bytestring integer)}
                      ds
                      {bool}
                      False
                      (\(ds :
                           Tuple
                             bytestring
                             ((\k v -> List (Tuple k v)) bytestring integer))
                        (rest :
                           List
                             (Tuple
                                bytestring
                                ((\k v -> List (Tuple k v))
                                   bytestring
                                   integer))) ->
                         Tuple_match
                           {bytestring}
                           {(\k v -> List (Tuple k v)) bytestring integer}
                           ds
                           {bool}
                           (\(c : bytestring)
                             (tokens :
                                (\k v -> List (Tuple k v))
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
    (\k v -> List (Tuple k v))
      bytestring
      ((\k v -> List (Tuple k v)) bytestring integer))
 (ds :
    (\k v -> List (Tuple k v))
      bytestring
      ((\k v -> List (Tuple k v)) bytestring integer)) ->
  goOuter ds ds
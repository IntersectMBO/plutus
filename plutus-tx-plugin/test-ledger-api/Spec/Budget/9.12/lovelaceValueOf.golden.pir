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
  !go : List (Tuple bytestring integer) -> integer
    = \(ds : List (Tuple bytestring integer)) ->
        List_match
          {Tuple bytestring integer}
          ds
          {all dead. integer}
          (/\dead -> 0)
          (\(ds : Tuple bytestring integer)
            (xs' : List (Tuple bytestring integer)) ->
             /\dead ->
               Tuple_match
                 {bytestring}
                 {integer}
                 ds
                 {integer}
                 (\(c' : bytestring) (i : integer) ->
                    case
                      (all dead. integer)
                      (equalsByteString # c')
                      [(/\dead -> go xs'), (/\dead -> i)]
                      {all dead. dead}))
          {all dead. dead}
in
letrec
  !go :
     List (Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer)) ->
     integer
    = \(ds :
          List
            (Tuple
               bytestring
               ((\k v -> List (Tuple k v)) bytestring integer))) ->
        List_match
          {Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer)}
          ds
          {all dead. integer}
          (/\dead -> 0)
          (\(ds :
               Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer))
            (xs' :
               List
                 (Tuple
                    bytestring
                    ((\k v -> List (Tuple k v)) bytestring integer))) ->
             /\dead ->
               Tuple_match
                 {bytestring}
                 {(\k v -> List (Tuple k v)) bytestring integer}
                 ds
                 {integer}
                 (\(c' : bytestring)
                   (i : (\k v -> List (Tuple k v)) bytestring integer) ->
                    case
                      (all dead. integer)
                      (equalsByteString # c')
                      [(/\dead -> go xs'), (/\dead -> go i)]
                      {all dead. dead}))
          {all dead. dead}
in
\(v :
    (\k v -> List (Tuple k v))
      bytestring
      ((\k v -> List (Tuple k v)) bytestring integer)) ->
  go v
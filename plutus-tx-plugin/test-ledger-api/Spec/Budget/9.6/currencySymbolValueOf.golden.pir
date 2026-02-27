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
  !go : List (Tuple2 bytestring integer) -> integer
    = \(ds : List (Tuple2 bytestring integer)) ->
        List_match
          {Tuple2 bytestring integer}
          ds
          {all dead. integer}
          (/\dead -> 0)
          (\(x : Tuple2 bytestring integer)
            (xs : List (Tuple2 bytestring integer)) ->
             /\dead ->
               Tuple2_match
                 {bytestring}
                 {integer}
                 x
                 {integer}
                 (\(ds : bytestring) (amt : integer) -> addInteger amt (go xs)))
          {all dead. dead}
in
\(value :
    (\k v -> List (Tuple2 k v))
      bytestring
      ((\k v -> List (Tuple2 k v)) bytestring integer))
 (cur : bytestring) ->
  letrec
    !go :
       List
         (Tuple2 bytestring ((\k v -> List (Tuple2 k v)) bytestring integer)) ->
       integer
      = \(ds :
            List
              (Tuple2
                 bytestring
                 ((\k v -> List (Tuple2 k v)) bytestring integer))) ->
          List_match
            {Tuple2 bytestring ((\k v -> List (Tuple2 k v)) bytestring integer)}
            ds
            {all dead. integer}
            (/\dead -> 0)
            (\(ds :
                 Tuple2
                   bytestring
                   ((\k v -> List (Tuple2 k v)) bytestring integer))
              (xs' :
                 List
                   (Tuple2
                      bytestring
                      ((\k v -> List (Tuple2 k v)) bytestring integer))) ->
               /\dead ->
                 Tuple2_match
                   {bytestring}
                   {(\k v -> List (Tuple2 k v)) bytestring integer}
                   ds
                   {integer}
                   (\(c' : bytestring)
                     (i : (\k v -> List (Tuple2 k v)) bytestring integer) ->
                      case
                        (all dead. integer)
                        (equalsByteString c' cur)
                        [(/\dead -> go xs'), (/\dead -> go i)]
                        {all dead. dead}))
            {all dead. dead}
  in
  go value
let
  data Unit | Unit_match where
    Unit : Unit
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  !`$j` :
     bytestring -> (\k v -> List (Tuple2 k v)) bytestring integer -> integer
    = \(ds : bytestring) (b : (\k v -> List (Tuple2 k v)) bytestring integer) ->
        List_match
          {Tuple2 bytestring integer}
          b
          {all dead. integer}
          (/\dead ->
             let
               !x : Unit = trace {Unit} "PT8" Unit
             in
             Tuple2_match
               {bytestring}
               {integer}
               (error {Tuple2 bytestring integer})
               {integer}
               (\(ds : bytestring) (b : integer) -> b))
          (\(x : Tuple2 bytestring integer)
            (ds : List (Tuple2 bytestring integer)) ->
             /\dead ->
               Tuple2_match
                 {bytestring}
                 {integer}
                 x
                 {integer}
                 (\(ds : bytestring) (b : integer) -> b))
          {all dead. dead}
in
\(ds :
    (\k v -> List (Tuple2 k v))
      bytestring
      ((\k v -> List (Tuple2 k v)) bytestring integer)) ->
  List_match
    {Tuple2 bytestring ((\k v -> List (Tuple2 k v)) bytestring integer)}
    ds
    {all dead. integer}
    (/\dead ->
       let
         !x : Unit = trace {Unit} "PT8" Unit
       in
       Tuple2_match
         {bytestring}
         {(\k v -> List (Tuple2 k v)) bytestring integer}
         (error
            {Tuple2
               bytestring
               ((\k v -> List (Tuple2 k v)) bytestring integer)})
         {integer}
         (\(ds : bytestring)
           (b : (\k v -> List (Tuple2 k v)) bytestring integer) ->
            `$j` ds b))
    (\(x : Tuple2 bytestring ((\k v -> List (Tuple2 k v)) bytestring integer))
      (ds :
         List
           (Tuple2
              bytestring
              ((\k v -> List (Tuple2 k v)) bytestring integer))) ->
       /\dead ->
         Tuple2_match
           {bytestring}
           {(\k v -> List (Tuple2 k v)) bytestring integer}
           x
           {integer}
           (\(ds : bytestring)
             (b : (\k v -> List (Tuple2 k v)) bytestring integer) ->
              `$j` ds b))
    {all dead. dead}
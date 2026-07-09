let
  data Unit | Unit_match where
    Unit : Unit
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
  !`$j` : (\k v -> List (Tuple k v)) bytestring integer -> integer
    = \(b : (\k v -> List (Tuple k v)) bytestring integer) ->
        List_match
          {Tuple bytestring integer}
          b
          {all dead. integer}
          (/\dead ->
             let
               !x : Unit = trace {Unit} "PT8" Unit
             in
             Tuple_match
               {bytestring}
               {integer}
               (error {Tuple bytestring integer})
               {integer}
               (\(ds : bytestring) (b : integer) -> b))
          (\(x : Tuple bytestring integer)
            (ds : List (Tuple bytestring integer)) ->
             /\dead ->
               Tuple_match
                 {bytestring}
                 {integer}
                 x
                 {integer}
                 (\(ds : bytestring) (b : integer) -> b))
          {all dead. dead}
in
\(ds :
    (\k v -> List (Tuple k v))
      bytestring
      ((\k v -> List (Tuple k v)) bytestring integer)) ->
  List_match
    {Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer)}
    ds
    {all dead. integer}
    (/\dead ->
       let
         !x : Unit = trace {Unit} "PT8" Unit
       in
       Tuple_match
         {bytestring}
         {(\k v -> List (Tuple k v)) bytestring integer}
         (error
            {Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer)})
         {integer}
         (\(ds : bytestring)
           (b : (\k v -> List (Tuple k v)) bytestring integer) ->
            `$j` b))
    (\(x : Tuple bytestring ((\k v -> List (Tuple k v)) bytestring integer))
      (ds :
         List
           (Tuple
              bytestring
              ((\k v -> List (Tuple k v)) bytestring integer))) ->
       /\dead ->
         Tuple_match
           {bytestring}
           {(\k v -> List (Tuple k v)) bytestring integer}
           x
           {integer}
           (\(ds : bytestring)
             (b : (\k v -> List (Tuple k v)) bytestring integer) ->
              `$j` b))
    {all dead. dead}
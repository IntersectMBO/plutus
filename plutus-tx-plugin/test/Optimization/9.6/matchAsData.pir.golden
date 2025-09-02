let
  data Unit | Unit_match where
    Unit : Unit
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
\(ds : (\a -> data) integer) ->
  Tuple2_match
    {integer}
    {list data}
    ((let
         b = list data
       in
       \(tup : pair integer b) ->
         Tuple2
           {integer}
           {b}
           (case integer tup [(\(l : integer) (r : b) -> l)])
           (case b tup [(\(l : integer) (r : b) -> r)]))
       (unConstrData ds))
    {integer}
    (\(ds : integer) (ds : list data) ->
       case
         (all dead. integer)
         (equalsInteger 0 ds)
         [ (/\dead ->
              Tuple2_match
                {integer}
                {list data}
                ((let
                     b = list data
                   in
                   \(tup : pair integer b) ->
                     Tuple2
                       {integer}
                       {b}
                       (case integer tup [(\(l : integer) (r : b) -> l)])
                       (case b tup [(\(l : integer) (r : b) -> r)]))
                   (unConstrData ds))
                {integer}
                (\(ds : integer) (ds : list data) ->
                   case
                     (all dead. integer)
                     (equalsInteger 1 ds)
                     [ (/\dead ->
                          let
                            !defaultBody : integer = error {integer}
                          in
                          Unit_match (error {Unit}) {integer} defaultBody)
                     , (/\dead -> 1) ]
                     {all dead. dead}))
         , (/\dead ->
              let
                !ds : data = headList {data} ds
                !ds : list data = tailList {data} ds
              in
              unIData ds) ]
         {all dead. dead})
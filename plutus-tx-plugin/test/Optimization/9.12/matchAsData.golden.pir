let
  data Unit | Unit_match where
    Unit : Unit
in
\(ds : (\a -> data) integer) ->
  let
    !tup : pair integer (list data) = unConstrData ds
  in
  case
    (all dead. integer)
    (equalsInteger 0 (case integer tup [(\(l : integer) (r : list data) -> l)]))
    [ (/\dead ->
         case
           (all dead. integer)
           (equalsInteger
              1
              (case
                 integer
                 (unConstrData ds)
                 [(\(l : integer) (r : list data) -> l)]))
           [ (/\dead ->
                let
                  !defaultBody : integer = error {integer}
                in
                Unit_match (error {Unit}) {integer} defaultBody)
           , (/\dead -> 1) ]
           {all dead. dead})
    , (/\dead ->
         unIData
           (headList
              {data}
              ((let
                   b = list data
                 in
                 \(x : pair integer b) ->
                   case b x [(\(l : integer) (r : b) -> r)])
                 tup))) ]
    {all dead. dead}
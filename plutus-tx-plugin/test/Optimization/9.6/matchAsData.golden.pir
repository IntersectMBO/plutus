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
           [ (/\dead -> case integer (error {unit}) [(error {integer})])
           , (/\dead -> 1) ]
           {all dead. dead})
    , (/\dead ->
         case
           integer
           ((let
                b = list data
              in
              \(x : pair integer b) -> case b x [(\(l : integer) (r : b) -> r)])
              tup)
           [(\(ds : data) (ds : list data) -> unIData ds)]) ]
    {all dead. dead}
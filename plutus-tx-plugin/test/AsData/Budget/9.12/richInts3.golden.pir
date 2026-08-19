let
  data Unit | Unit_match where
    Unit : Unit
in
\(d : data) ->
  case
    integer
    (dropList
       {data}
       3
       ((let
            b = list data
          in
          \(x : pair integer b) -> case b x [(\(l : integer) (r : b) -> r)])
          (unConstrData d)))
    [ (\(ds : data) (ds : list data) ->
         case
           integer
           (dropList {data} 3 ds)
           [ (\(ds : data) (ds : list data) ->
                case
                  integer
                  (dropList {data} 6 ds)
                  [ (\(ds : data) (ds : list data) ->
                       addInteger
                         (unIData ds)
                         (addInteger (unIData ds) (unIData ds))) ]) ]) ]
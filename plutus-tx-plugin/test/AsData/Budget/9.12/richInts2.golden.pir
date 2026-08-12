let
  data Unit | Unit_match where
    Unit : Unit
in
\(d : data) ->
  case
    integer
    (dropList
       {data}
       8
       ((let
            b = list data
          in
          \(x : pair integer b) -> case b x [(\(l : integer) (r : b) -> r)])
          (unConstrData d)))
    [ (\(ds : data) (ds : list data) ->
         case
           integer
           (dropList {data} 4 ds)
           [ (\(ds : data) (ds : list data) ->
                addInteger (unIData ds) (unIData ds)) ]) ]
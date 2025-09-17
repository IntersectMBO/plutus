let
  data Unit | Unit_match where
    Unit : Unit
in
\(d : data) ->
  unIData
    (headList
       {data}
       ((let
            b = list data
          in
          \(x : pair integer b) -> case b x [(\(l : integer) (r : b) -> r)])
          (unConstrData d)))
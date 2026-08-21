\(d : data) ->
  unIData
    (headList
       {data}
       (dropList
          {data}
          15
          ((let
               b = list data
             in
             \(x : pair integer b) -> case b x [(\(l : integer) (r : b) -> r)])
             (unConstrData d))))
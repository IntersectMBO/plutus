let
  data Unit | Unit_match where
    Unit : Unit
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
\(d : data) ->
  Tuple2_match
    {data}
    {list data}
    (let
      !l : list data
        = (let
              b = list data
            in
            \(x : pair integer b) -> case b x [(\(l : integer) (r : b) -> r)])
            (unConstrData d)
    in
    Tuple2 {data} {list data} (headList {data} l) (tailList {data} l))
    {integer}
    (\(ds : data) (ds : list data) ->
       let
         !ds : data = headList {data} ds
         !ds : list data = tailList {data} ds
         !ds : data = headList {data} ds
         !ds : list data = tailList {data} ds
       in
       unIData ds)
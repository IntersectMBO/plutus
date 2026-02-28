let
  data Unit | Unit_match where
    Unit : Unit
  !addInteger : integer -> integer -> integer
    = \(x : integer) (y : integer) -> addInteger x y
  !lessThanInteger : integer -> integer -> bool
    = \(x : integer) (y : integer) -> lessThanInteger x y
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
         !x : integer = unIData ds
         !y : integer = unIData ds
         !z : integer = unIData ds
         !w : integer = unIData (headList {data} ds)
       in
       addInteger
         (addInteger
            (addInteger (addInteger (addInteger x y) z) w)
            (case
               (all dead. integer)
               (lessThanInteger (addInteger y z) (addInteger x w))
               [(/\dead -> addInteger y w), (/\dead -> addInteger x z)]
               {all dead. dead}))
         (case
            (all dead. integer)
            (lessThanInteger (addInteger z y) (addInteger w x))
            [(/\dead -> addInteger w y), (/\dead -> addInteger z x)]
            {all dead. dead}))
let
  data Unit | Unit_match where
    Unit : Unit
  !addInteger : integer -> integer -> integer
    = \(x : integer) (y : integer) -> addInteger x y
  !lessThanInteger : integer -> integer -> bool
    = \(x : integer) (y : integer) -> lessThanInteger x y
in
\(d : data) ->
  let
    !l : list data
      = (let
            b = list data
          in
          \(x : pair integer b) -> case b x [(\(l : integer) (r : b) -> r)])
          (unConstrData d)
    !l : list data = tailList {data} l
    !l : list data = tailList {data} l
    !x : integer = unIData (headList {data} l)
    !y : integer = unIData (headList {data} l)
    !z : integer = unIData (headList {data} l)
    !w : integer = unIData (headList {data} (tailList {data} l))
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
       {all dead. dead})
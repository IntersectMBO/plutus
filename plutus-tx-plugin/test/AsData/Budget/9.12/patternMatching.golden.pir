let
  data Unit | Unit_match where
    Unit : Unit
  !addInteger : integer -> integer -> integer
    = \(x : integer) (y : integer) -> addInteger x y
  !lessThanInteger : integer -> integer -> bool
    = \(x : integer) (y : integer) -> lessThanInteger x y
in
\(d : data) ->
  case
    integer
    ((let
         b = list data
       in
       \(x : pair integer b) -> case b x [(\(l : integer) (r : b) -> r)])
       (unConstrData d))
    [ (\(ds : data) (ds : list data) ->
         case
           integer
           ds
           [ (\(ds : data) (ds : list data) ->
                case
                  integer
                  ds
                  [ (\(ds : data) (ds : list data) ->
                       let
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
                               (lessThanInteger
                                  (addInteger y z)
                                  (addInteger x w))
                               [ (/\dead -> addInteger y w)
                               , (/\dead -> addInteger x z) ]
                               {all dead. dead}))
                         (case
                            (all dead. integer)
                            (lessThanInteger (addInteger z y) (addInteger w x))
                            [ (/\dead -> addInteger w y)
                            , (/\dead -> addInteger z x) ]
                            {all dead. dead})) ]) ]) ]
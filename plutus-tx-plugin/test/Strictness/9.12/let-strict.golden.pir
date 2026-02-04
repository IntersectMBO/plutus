let
  data Unit | Unit_match where
    Unit : Unit
in
\(m : integer) ->
  case
    (all dead. integer)
    (lessThanInteger m 0)
    [ (/\dead -> m)
    , (/\dead ->
         addInteger
           (error {integer -> integer} m)
           (error {integer -> integer} m)) ]
    {all dead. dead}
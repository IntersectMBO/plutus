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
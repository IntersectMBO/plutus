(\(x : integer) (y : integer) (z : integer) ->
   case
     (all dead. bool)
     (lessThanInteger x 100)
     [ (/\dead -> False)
     , (/\dead ->
          case
            (all dead. bool)
            (lessThanInteger y 100)
            [(/\dead -> False), (/\dead -> lessThanInteger z 100)]
            {all dead. dead}) ]
     {all dead. dead})
  50
  60
  150
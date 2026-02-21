(let
    !ifThenElse : all a. bool -> a -> a -> a
      = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
  in
  \(x : integer) (y : integer) (z : integer) ->
    case
      (all dead. bool)
      (ifThenElse {bool} (lessThanInteger x 100) False True)
      [ (/\dead ->
           case
             (all dead. bool)
             (ifThenElse {bool} (lessThanInteger y 100) False True)
             [ (/\dead ->
                  case
                    bool
                    (ifThenElse {bool} (lessThanInteger z 100) False True)
                    [True, False])
             , (/\dead -> False) ]
             {all dead. dead})
      , (/\dead -> False) ]
      {all dead. dead})
  150
  60
  70
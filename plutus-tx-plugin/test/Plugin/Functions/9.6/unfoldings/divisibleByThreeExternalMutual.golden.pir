let
  !equalsInteger : integer -> integer -> bool = equalsInteger
  !subtractInteger : integer -> integer -> integer = subtractInteger
in
letrec
  ~divisibleByThreeDirect : integer -> bool
    = \(n : integer) ->
        let
          !n : integer = n
        in
        case
          (all dead. bool)
          (equalsInteger n 0)
          [ (/\dead ->
               (\(n : integer) ->
                  let
                    !n : integer = n
                  in
                  case
                    (all dead. bool)
                    (equalsInteger n 0)
                    [ (/\dead ->
                         (\(n : integer) ->
                            let
                              !n : integer = n
                            in
                            case
                              (all dead. bool)
                              (equalsInteger n 0)
                              [ (/\dead ->
                                   divisibleByThreeDirect (subtractInteger n 1))
                              , (/\dead -> False) ]
                              {all dead. dead})
                           (subtractInteger n 1))
                    , (/\dead -> False) ]
                    {all dead. dead})
                 (subtractInteger n 1))
          , (/\dead -> True) ]
          {all dead. dead}
in
divisibleByThreeDirect
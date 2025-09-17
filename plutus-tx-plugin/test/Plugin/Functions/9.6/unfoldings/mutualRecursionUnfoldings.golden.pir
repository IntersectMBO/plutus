let
  !equalsInteger : integer -> integer -> bool = equalsInteger
  !subtractInteger : integer -> integer -> integer = subtractInteger
in
letrec
  ~evenDirect : integer -> bool
    = \(n : integer) ->
        let
          !n : integer = n
        in
        case
          (all dead. bool)
          (equalsInteger n 0)
          [(/\dead -> oddDirect (subtractInteger n 1)), (/\dead -> True)]
          {all dead. dead}
  ~oddDirect : integer -> bool
    = \(n : integer) ->
        let
          !n : integer = n
        in
        case
          (all dead. bool)
          (equalsInteger n 0)
          [(/\dead -> evenDirect (subtractInteger n 1)), (/\dead -> False)]
          {all dead. dead}
in
evenDirect 4
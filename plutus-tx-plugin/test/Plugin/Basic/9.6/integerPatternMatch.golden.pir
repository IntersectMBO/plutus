let
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  ~integerMatchFunction : integer -> integer
    = \(ds : integer) ->
        let
          !ds : integer = ds
        in
        case
          (all dead. integer)
          (equalsInteger ds 1)
          [ (/\dead -> case integer (equalsInteger ds 2) [42, 22])
          , (/\dead -> 12) ]
          {all dead. dead}
in
integerMatchFunction 2
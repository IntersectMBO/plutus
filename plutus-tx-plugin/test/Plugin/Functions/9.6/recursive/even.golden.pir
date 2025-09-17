let
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  !subtractInteger : integer -> integer -> integer = subtractInteger
  ~subtractInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in subtractInteger x y
in
letrec
  ~even : integer -> bool
    = \(n : integer) ->
        let
          !n : integer = n
        in
        case
          (all dead. bool)
          (equalsInteger n 0)
          [ (/\dead ->
               let
                 !n : integer = subtractInteger n 1
               in
               case
                 (all dead. bool)
                 (equalsInteger n 0)
                 [(/\dead -> even (subtractInteger n 1)), (/\dead -> False)]
                 {all dead. dead})
          , (/\dead -> True) ]
          {all dead. dead}
in
even
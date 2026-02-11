let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
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
  ~fib : integer -> integer
    = \(n : integer) ->
        let
          !n : integer = n
        in
        case
          (all dead. integer)
          (equalsInteger n 0)
          [ (/\dead ->
               case
                 (all dead. integer)
                 (equalsInteger n 1)
                 [ (/\dead ->
                      addInteger
                        (fib (subtractInteger n 1))
                        (fib (subtractInteger n 2)))
                 , (/\dead -> 1) ]
                 {all dead. dead})
          , (/\dead -> 0) ]
          {all dead. dead}
in
fib
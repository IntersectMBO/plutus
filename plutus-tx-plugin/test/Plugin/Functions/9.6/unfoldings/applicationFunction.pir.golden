let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~myDollar : all a b. (a -> b) -> a -> b
    = /\a b ->
        \(f : a -> b) ->
          let
            !f : a -> b = f
          in
          \(a : a) -> let !a : a = a in f a
in
myDollar
  {integer}
  {integer}
  (\(x : integer) -> let !x : integer = x in addInteger 1 x)
  1
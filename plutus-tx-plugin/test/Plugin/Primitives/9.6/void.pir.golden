let
  ~fail : unit -> bool = \(ds : unit) -> False
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
in
\(ds : integer) ->
  let
    !ds : integer = ds
  in
  \(ds : integer) ->
    let
      !ds : integer = ds
      !x' : bool = equalsInteger ds ds
      !y' : bool = equalsInteger ds ds
    in
    case
      (all dead. bool)
      x'
      [ (/\dead -> fail ())
      , (/\dead ->
           case (all dead. bool) y' [(/\dead -> fail ()), (/\dead -> True)]
             {all dead. dead}) ]
      {all dead. dead}
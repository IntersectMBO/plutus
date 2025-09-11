let
  data Unit | Unit_match where
    Unit : Unit
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !unitval : unit = ()
  ~joinError : bool -> bool -> Unit
    = \(x : bool) ->
        let
          !x : bool = x
        in
        \(y : bool) ->
          let
            !y : bool = y
          in
          case
            (all dead. Unit)
            x
            [ (/\dead -> Unit)
            , (/\dead ->
                 case
                   (all dead. Unit)
                   y
                   [(/\dead -> Unit), (/\dead -> error {Unit} unitval)]
                   {all dead. dead}) ]
            {all dead. dead}
in
joinError
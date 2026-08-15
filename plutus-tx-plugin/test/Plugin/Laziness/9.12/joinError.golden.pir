let
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
  !unitval : unit = ()
  ~joinError : bool -> bool -> unit
    = \(x : bool) ->
        let
          !x : bool = x
        in
        \(y : bool) ->
          let
            !y : bool = y
          in
          case
            (all dead. unit)
            x
            [ (/\dead -> ())
            , (/\dead ->
                 case
                   (all dead. unit)
                   y
                   [(/\dead -> ()), (/\dead -> error {unit} unitval)]
                   {all dead. dead}) ]
            {all dead. dead}
in
joinError
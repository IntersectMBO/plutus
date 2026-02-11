(let
    data Unit | Unit_match where
      Unit : Unit
  in
  \(x : integer) (y : integer) (z : integer) ->
    case
      (unit -> unit)
      (lessThanInteger x 100)
      [ (\(ds : unit) ->
           let
             !x : Unit = trace {Unit} "conditions not met" Unit
           in
           error {unit})
      , (\(ds : unit) ->
           case
             (unit -> unit)
             (lessThanInteger y 100)
             [ (\(ds : unit) ->
                  let
                    !x : Unit = trace {Unit} "conditions not met" Unit
                  in
                  error {unit})
             , (\(ds : unit) ->
                  case
                    (unit -> unit)
                    (lessThanInteger z 100)
                    [ (\(ds : unit) ->
                         let
                           !x : Unit = trace {Unit} "conditions not met" Unit
                         in
                         error {unit})
                    , (\(ds : unit) -> ()) ]
                    ()) ]
             ()) ]
      ())
  50
  60
  150
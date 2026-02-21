(let
    data Unit | Unit_match where
      Unit : Unit
  in
  \(x : integer) (y : integer) (z : integer) ->
    let
      !b : bool = lessThanInteger x 100
      !b : bool = lessThanInteger y 100
      !b : bool = lessThanInteger z 100
      !b : bool
        = case (unit -> bool) b [(\(ds : unit) -> False), (\(ds : unit) -> b)]
            ()
    in
    case
      (unit -> unit)
      (case (unit -> bool) b [(\(ds : unit) -> False), (\(ds : unit) -> b)] ())
      [ (\(ds : unit) ->
           let
             !x : Unit = trace {Unit} "conditions not met" Unit
           in
           error {unit})
      , (\(ds : unit) -> ()) ]
      ())
  150
  60
  70
\(ds : list integer) ->
  (let
      r = unit -> integer
    in
    \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
      case r xs [f, z])
    (\(ds : unit) -> let !x : unit = trace {unit} "PT23" () in error {integer})
    (\(x : integer) (xs : list integer) (ds : unit) -> x)
    []
    ()
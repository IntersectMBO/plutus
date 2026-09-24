\(ds : list integer) ->
  (let
      r = unit -> list integer
    in
    \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
      case r xs [f, z])
    (\(ds : unit) ->
       let
         !x : unit = trace {unit} "PT25" ()
       in
       error {list integer})
    (\(x : integer) (xs : list integer) (ds : unit) -> xs)
    []
    ()
\(xs : list integer) ->
  let
    !l : list integer = dropList {integer} 10 xs
  in
  (let
      r = unit -> unit -> integer
    in
    \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
      case r xs [f, z])
    (\(_ann : unit) ->
       let
         !x : unit = trace {unit} "PT22" ()
       in
       error {unit -> integer})
    (\(x : integer) (xs : list integer) (ds : unit) (_ann : unit) -> x)
    l
    ()
    ()
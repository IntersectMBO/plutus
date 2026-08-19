let
  data Unit | Unit_match where
    Unit : Unit
in
\(xs : list integer) ->
  let
    !x : Unit = trace {Unit} "PT21" Unit
  in
  error {integer}
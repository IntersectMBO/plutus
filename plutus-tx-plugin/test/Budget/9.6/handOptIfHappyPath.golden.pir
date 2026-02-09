let
  !ifThenElse : all a. bool -> a -> a -> a
    = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
  !greaterThanInteger : integer -> integer -> bool
    = \(x : integer) (y : integer) ->
        ifThenElse {bool} (lessThanEqualsInteger x y) False True
  data Unit | Unit_match where
    Unit : Unit
  !traceError : all a. string -> a
    = /\a ->
        \(str : string) -> let !x : Unit = trace {Unit} str Unit in error {a}
in
\(x : integer) (y : integer) ->
  ifThenElse
    {unit -> bool}
    (greaterThanInteger x 10)
    (\(ds : unit) -> traceError {bool} "x too large")
    (\(ds : unit) ->
       ifThenElse
         {unit -> bool}
         (lessThanInteger y 0)
         (\(ds : unit) -> traceError {bool} "y negative")
         (\(ds : unit) ->
            ifThenElse
              {unit -> bool}
              (greaterThanInteger (addInteger x y) 20)
              (\(ds : unit) -> traceError {bool} "sum too large")
              (\(ds : unit) -> True)
              ())
         ())
    ()
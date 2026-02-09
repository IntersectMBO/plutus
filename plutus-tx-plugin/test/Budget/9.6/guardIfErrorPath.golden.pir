let
  data Unit | Unit_match where
    Unit : Unit
  !traceError : all a. string -> a
    = /\a ->
        \(str : string) -> let !x : Unit = trace {Unit} str Unit in error {a}
in
\(x : integer) (y : integer) ->
  case
    (all dead. bool)
    (case bool (lessThanEqualsInteger x 10) [True, False])
    [ (/\dead ->
         case
           (all dead. bool)
           (lessThanInteger y 0)
           [ (/\dead ->
                case
                  (all dead. bool)
                  (case
                     bool
                     (lessThanEqualsInteger (addInteger x y) 20)
                     [True, False])
                  [ (/\dead -> True)
                  , (/\dead -> traceError {bool} "sum too large") ]
                  {all dead. dead})
           , (/\dead -> traceError {bool} "y negative") ]
           {all dead. dead})
    , (/\dead -> traceError {bool} "x too large") ]
    {all dead. dead}
(program
   1.1.0
   (\x y ->
      (\traceError ->
         case
           (lessThanEqualsInteger x 10)
           [ (\ds -> traceError "x too large")
           , (\ds ->
                case
                  (lessThanInteger y 0)
                  [ (\ds ->
                       case
                         (lessThanEqualsInteger (addInteger x y) 20)
                         [(\ds -> traceError "sum too large"), (\ds -> True)]
                         ())
                  , (\ds -> traceError "y negative") ]
                  ()) ])
        (\str -> (\x -> error) (force trace str (constr 0 [])))
        ()))
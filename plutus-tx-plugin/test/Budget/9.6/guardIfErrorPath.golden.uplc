(program
   1.1.0
   (\x y ->
      force
        ((\traceError ->
            case
              (lessThanEqualsInteger x 10)
              [ (delay (traceError "x too large"))
              , (delay
                   (case
                      (lessThanInteger y 0)
                      [ (case
                           (lessThanEqualsInteger (addInteger x y) 20)
                           [(traceError "sum too large"), True])
                      , (traceError "y negative") ])) ])
           (\str -> (\x -> error) (force trace str (constr 0 []))))))
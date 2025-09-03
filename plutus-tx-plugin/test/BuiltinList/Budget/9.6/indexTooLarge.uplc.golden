(program
   1.1.0
   (\xs ->
      force
        ((\traceError ->
            case
              (lessThanInteger 10 0)
              [ (delay
                   (case
                      (force dropList 10 xs)
                      [(\x xs ds _ann -> x), (\_ann -> traceError "PT22")]
                      (constr 0 [])
                      (constr 0 [])))
              , (delay (traceError "PT21")) ])
           (\str -> (\x -> error) (force trace str (constr 0 []))))))
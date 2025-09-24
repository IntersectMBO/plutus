(program
   1.1.0
   (\xs ->
      (\i ->
         force
           ((\traceError ->
               case
                 (lessThanInteger i 0)
                 [ (delay
                      (case
                         (force dropList i xs)
                         [(\x xs ds _ann -> x), (\_ann -> traceError "PT22")]
                         (constr 0 [])
                         (constr 0 [])))
                 , (delay (traceError "PT21")) ])
              (\str -> (\x -> error) (force trace str (constr 0 [])))))
        (subtractInteger 0 1)))
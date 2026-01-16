(program
   1.1.0
   (\xs ->
      force
        ((\traceError ->
            (\cse ->
               case
                 (lessThanInteger cse 0)
                 [ (delay
                      (case
                         (force dropList cse xs)
                         [(\x xs ds _ann -> x), (\_ann -> traceError "PT22")]
                         (constr 0 [])
                         (constr 0 [])))
                 , (delay (traceError "PT21")) ])
              (subtractInteger 0 1))
           (\str -> (\x -> error) (force trace str (constr 0 []))))))
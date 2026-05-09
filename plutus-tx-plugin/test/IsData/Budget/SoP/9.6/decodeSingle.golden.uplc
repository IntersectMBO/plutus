(program
   1.1.0
   (\d ->
      (\p ->
         (\index ->
            (\args ->
               case
                 (force
                    (case
                       (constr 0
                          [ (equalsInteger 0 index)
                          , (delay
                               (\ds ->
                                  constr 0 [(unIData (force headList ds))]))
                          , (delay error) ])
                       [(force ifThenElse)])
                    args)
                 [(\x -> x)])
              (force (force sndPair) p))
           (force (force fstPair) p))
        (unConstrData d)))
(program
   1.1.0
   (\d ->
      (\p ->
         (\args ->
            case
              (force
                 (case
                    (constr 0
                       [ (equalsInteger 0 (force (force fstPair) p))
                       , (delay
                            (\ds -> constr 0 [(unIData (force headList ds))]))
                       , (delay error) ])
                    [(force ifThenElse)])
                 args)
              [(\x -> x)])
           (force (force sndPair) p))
        (unConstrData d)))
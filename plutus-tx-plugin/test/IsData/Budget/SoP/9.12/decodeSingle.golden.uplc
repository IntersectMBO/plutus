(program
   1.1.0
   (\d ->
      case
        ((\p ->
            (\args ->
               force
                 (case
                    (constr 0
                       [ (equalsInteger 0 (force (force fstPair) p))
                       , (delay
                            (\ds -> constr 0 [(unIData (force headList ds))]))
                       , (delay error) ])
                    [(force ifThenElse)])
                 args)
              (force (force sndPair) p))
           (unConstrData d))
        [(\x -> x)]))
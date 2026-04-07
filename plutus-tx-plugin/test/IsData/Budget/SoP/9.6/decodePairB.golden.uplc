(program
   1.1.0
   (\d ->
      (\p ->
         case
           ((\index args ->
               force
                 (case
                    (constr 0
                       [ (equalsInteger 0 index)
                       , (delay
                            (\ds -> constr 0 [(unIData (force headList ds))]))
                       , (delay
                            (force
                               (case
                                  (constr 0
                                     [ (equalsInteger 1 index)
                                     , (delay
                                          (\ds ->
                                             constr 1
                                               [(unIData (force headList ds))]))
                                     , (delay error) ])
                                  [(force ifThenElse)]))) ])
                    [(force ifThenElse)])
                 args)
              (force (force fstPair) p)
              (force (force sndPair) p))
           [(\x -> x), (\x -> addInteger 1 x)])
        (unConstrData d)))
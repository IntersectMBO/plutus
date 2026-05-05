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
                          , (delay
                               (force
                                  (case
                                     (constr 0
                                        [ (equalsInteger 1 index)
                                        , (delay
                                             (\ds ->
                                                constr 1
                                                  [ (unIData
                                                       (force headList ds)) ]))
                                        , (delay error) ])
                                     [(force ifThenElse)]))) ])
                       [(force ifThenElse)])
                    args)
                 [(\x -> x), (\x -> addInteger 1 x)])
              (force (force sndPair) p))
           (force (force fstPair) p))
        (unConstrData d)))
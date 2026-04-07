(program
   1.1.0
   (\d ->
      case
        ((\p ->
            (\index args ->
               force
                 (force ifThenElse
                    (equalsInteger 0 index)
                    (delay (\ds -> constr 0 []))
                    (delay
                       (force
                          (force ifThenElse
                             (equalsInteger 1 index)
                             (delay
                                (\ds ->
                                   constr 1 [(unIData (force headList ds))]))
                             (delay
                                (force
                                   (force ifThenElse
                                      (equalsInteger 2 index)
                                      (delay
                                         (\ds ->
                                            constr 2
                                              [ (unIData (force headList ds))
                                              , (unIData
                                                   (force headList
                                                      (force tailList ds))) ]))
                                      (delay error))))))))
                 args)
              (force (force fstPair) p)
              (force (force sndPair) p))
           (unConstrData d))
        [0, (\x -> x), (\x y -> addInteger x y)]))
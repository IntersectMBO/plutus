(program
   1.1.0
   (\d ->
      case
        ((\p ->
            (\index args ->
               force
                 (force ifThenElse
                    (equalsInteger 0 index)
                    (delay (\ds -> constr 0 [(unIData (force headList ds))]))
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
                                              [(unIData (force headList ds))]))
                                      (delay error))))))))
                 args)
              (force (force fstPair) p)
              (force (force sndPair) p))
           (unConstrData d))
        [(\x -> x), (\x -> addInteger 100 x), (\x -> addInteger 200 x)]))
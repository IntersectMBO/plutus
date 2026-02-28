(program
   1.1.0
   (\d ->
      (\cse ->
         (\cse ->
            (\cse ->
               (\cse ->
                  (\cse ->
                     addInteger
                       (addInteger
                          (addInteger (addInteger (addInteger cse cse) cse) cse)
                          (case
                             (lessThanInteger
                                (addInteger cse cse)
                                (addInteger cse cse))
                             [(addInteger cse cse), (addInteger cse cse)]))
                       (case
                          (lessThanInteger
                             (addInteger cse cse)
                             (addInteger cse cse))
                          [(addInteger cse cse), (addInteger cse cse)]))
                    (cse (\ds ds ds ds -> ds) (\void -> error)))
                 (cse (\ds ds ds ds -> ds) (\void -> error)))
              (cse (\ds ds ds ds -> ds) (\void -> error)))
           (cse (\ds ds ds ds -> ds) (\void -> error)))
        (\cont fail ->
           case
             ((\l -> constr 0 [(force headList l), (force tailList l)])
                (case (unConstrData d) [(\l r -> r)]))
             [ (\ds ds ->
                  (\ds ->
                     (\ds ->
                        (\ds ->
                           (\ds ->
                              cont
                                (unIData ds)
                                (unIData ds)
                                (unIData ds)
                                (unIData (force headList ds)))
                             (force tailList ds))
                          (force headList ds))
                       (force tailList ds))
                    (force headList ds)) ])))
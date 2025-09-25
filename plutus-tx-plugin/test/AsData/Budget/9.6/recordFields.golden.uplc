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
           (\l ->
              (\l ->
                 (\l ->
                    cont
                      (unIData (force headList l))
                      (unIData (force headList l))
                      (unIData (force headList l))
                      (unIData (force headList (force tailList l))))
                   (force tailList l))
                (force tailList l))
             (case (unConstrData d) [(\l r -> r)]))))
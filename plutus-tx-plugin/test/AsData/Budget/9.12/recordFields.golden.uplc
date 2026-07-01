(program
   1.1.0
   ((\forced forced d ->
       (\cse ->
          (\cse ->
             (\cse ->
                (\cse ->
                   (\cse ->
                      addInteger
                        (addInteger
                           (addInteger
                              (addInteger (addInteger cse cse) cse)
                              cse)
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
                     case
                       (constr 0
                          [ (unIData (forced l))
                          , (unIData (forced l))
                          , (unIData (forced l))
                          , (unIData (forced (forced l))) ])
                       [cont])
                    (forced l))
                 (forced l))
              (case (unConstrData d) [(\l r -> r)])))
      (force tailList)
      (force headList)))
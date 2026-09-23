(program
   1.1.0
   ((\forced d ->
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
            case
              (case (unConstrData d) [(\l r -> r)])
              [ (\ds ds ->
                   case
                     ds
                     [ (\ds ds ->
                          case
                            ds
                            [ (\ds ds ->
                                 case
                                   (constr 0
                                      [ (unIData ds)
                                      , (unIData ds)
                                      , (unIData ds)
                                      , (unIData (forced ds)) ])
                                   [cont]) ]) ]) ]))
      (force headList)))
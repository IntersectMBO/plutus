(program
   1.1.0
   (\d ->
      (\cse ->
         case
           (equalsInteger 0 (case cse [(\l r -> l)]))
           [ (case
                (equalsInteger 1 (case cse [(\l r -> l)]))
                [ (case
                     (equalsInteger 2 (case cse [(\l r -> l)]))
                     [ (case error [error])
                     , ((\cse ->
                           (\cse ->
                              (\cse ->
                                 (\y ->
                                    (\cse ->
                                       cse
                                         (cse cse)
                                         (\x y z w ->
                                            cse
                                              y
                                              (\x y z w ->
                                                 (\cse ->
                                                    constrData
                                                      0
                                                      (cse
                                                         (iData
                                                            (addInteger x x))
                                                         (cse
                                                            (iData
                                                               (addInteger y y))
                                                            (cse
                                                               (iData
                                                                  (addInteger
                                                                     z
                                                                     z))
                                                               (cse
                                                                  (iData
                                                                     (addInteger
                                                                        w
                                                                        w))
                                                                  [])))))
                                                   (force mkCons))
                                              (\void -> case error [error])))
                                      (\scrut cont fail ->
                                         (\cse ->
                                            (\cse ->
                                               (\cse ->
                                                  cont
                                                    (unIData (cse cse))
                                                    (unIData (cse cse))
                                                    (unIData (cse cse))
                                                    (unIData (cse (cse cse))))
                                                 (cse cse))
                                              (cse cse))
                                           (case
                                              (unConstrData scrut)
                                              [(\l r -> r)]))
                                      (\void -> case error [error]))
                                   (cse (cse cse)))
                                (case cse [(\l r -> r)]))
                             (force tailList))
                          (force headList)) ])
                , (force headList (case cse [(\l r -> r)])) ])
           , (force headList (case cse [(\l r -> r)])) ])
        (unConstrData d)))
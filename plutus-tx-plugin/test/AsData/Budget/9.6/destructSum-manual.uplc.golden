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
                     [ ((\cse -> case cse [cse]) error)
                     , ((\args ->
                           (\y ->
                              (\`$mInts` ->
                                 `$mInts`
                                   (force headList args)
                                   (\x y z w ->
                                      `$mInts`
                                        y
                                        (\x y z w ->
                                           constrData
                                             0
                                             (force mkCons
                                                (iData (addInteger x x))
                                                (force mkCons
                                                   (iData (addInteger y y))
                                                   (force mkCons
                                                      (iData (addInteger z z))
                                                      (force mkCons
                                                         (iData
                                                            (addInteger w w))
                                                         [])))))
                                        (\void ->
                                           (\cse -> case cse [cse]) error)))
                                (\scrut cont fail ->
                                   (\l ->
                                      (\l ->
                                         (\l ->
                                            cont
                                              (unIData (force headList l))
                                              (unIData (force headList l))
                                              (unIData (force headList l))
                                              (unIData
                                                 (force headList
                                                    (force tailList l))))
                                           (force tailList l))
                                        (force tailList l))
                                     (case (unConstrData scrut) [(\l r -> r)]))
                                (\void -> (\cse -> case cse [cse]) error))
                             (force headList (force tailList args)))
                          (case cse [(\l r -> r)])) ])
                , (force headList (case cse [(\l r -> r)])) ])
           , (force headList (case cse [(\l r -> r)])) ])
        (unConstrData d)))
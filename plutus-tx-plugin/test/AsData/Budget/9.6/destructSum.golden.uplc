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
                     , ((\l ->
                           (\`$mInts` ->
                              `$mInts`
                                (force headList l)
                                (\x y z w ->
                                   case
                                     (constr 0
                                        [ (force headList (force tailList l))
                                        , (\x y z w ->
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
                                        , (\void ->
                                             (\cse -> case cse [cse]) error) ])
                                     [`$mInts`]))
                             (\scrut cont fail ->
                                (\l ->
                                   (\l ->
                                      (\l ->
                                         case
                                           (constr 0
                                              [ (unIData (force headList l))
                                              , (unIData (force headList l))
                                              , (unIData (force headList l))
                                              , (unIData
                                                   (force headList
                                                      (force tailList l))) ])
                                           [cont])
                                        (force tailList l))
                                     (force tailList l))
                                  (case (unConstrData scrut) [(\l r -> r)]))
                             (\void -> (\cse -> case cse [cse]) error))
                          (case cse [(\l r -> r)])) ])
                , (force headList (case cse [(\l r -> r)])) ])
           , (force headList (case cse [(\l r -> r)])) ])
        (unConstrData d)))
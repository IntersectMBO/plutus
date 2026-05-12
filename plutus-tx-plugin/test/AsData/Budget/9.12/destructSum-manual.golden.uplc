(program
   1.1.0
   ((\forced
      forced
      forced
      d ->
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
                                  case
                                    (constr 0
                                       [ (forced args)
                                       , (\x
                                           y
                                           z
                                           w ->
                                            case
                                              (constr 0
                                                 [ y
                                                 , (\x
                                                     y
                                                     z
                                                     w ->
                                                      constrData
                                                        0
                                                        (forced
                                                           (iData
                                                              (addInteger x x))
                                                           (forced
                                                              (iData
                                                                 (addInteger
                                                                    y
                                                                    y))
                                                              (forced
                                                                 (iData
                                                                    (addInteger
                                                                       z
                                                                       z))
                                                                 (forced
                                                                    (iData
                                                                       (addInteger
                                                                          w
                                                                          w))
                                                                    [])))))
                                                 , (\void ->
                                                      (\cse -> case cse [cse])
                                                        error) ])
                                              [`$mInts`])
                                       , (\void ->
                                            (\cse -> case cse [cse]) error) ])
                                    [`$mInts`])
                                 (\scrut cont fail ->
                                    (\l ->
                                       (\l ->
                                          (\l ->
                                             case
                                               (constr 0
                                                  [ (unIData (forced l))
                                                  , (unIData (forced l))
                                                  , (unIData (forced l))
                                                  , (unIData
                                                       (forced (forced l))) ])
                                               [cont])
                                            (forced l))
                                         (forced l))
                                      (case
                                         (unConstrData scrut)
                                         [(\l r -> r)])))
                              (forced (forced args)))
                           (case cse [(\l r -> r)])) ])
                 , (forced (case cse [(\l r -> r)])) ])
            , (forced (case cse [(\l r -> r)])) ])
         (unConstrData d))
      (force mkCons)
      (force tailList)
      (force headList)))
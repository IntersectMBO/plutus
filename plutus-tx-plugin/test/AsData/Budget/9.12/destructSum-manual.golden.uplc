(program
   1.1.0
   (case
      (constr 0 [(force mkCons), (force tailList), (force headList)])
      [ (\forced
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
                                                                  (addInteger
                                                                     x
                                                                     x))
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
                                                          (\cse ->
                                                             case cse [cse])
                                                            error) ])
                                                  [`$mInts`])
                                           , (\void ->
                                                (\cse -> case cse [cse])
                                                  error) ])
                                        [`$mInts`])
                                     (\scrut
                                       cont
                                       fail ->
                                        case
                                          (case
                                             (unConstrData scrut)
                                             [(\l r -> r)])
                                          [ (\ds
                                              ds ->
                                               case
                                                 ds
                                                 [ (\ds
                                                     ds ->
                                                      case
                                                        ds
                                                        [ (\ds
                                                            ds ->
                                                             case
                                                               (constr 0
                                                                  [ (unIData ds)
                                                                  , (unIData ds)
                                                                  , (unIData ds)
                                                                  , (unIData
                                                                       (forced
                                                                          ds)) ])
                                                               [cont]) ]) ]) ]))
                                  (forced (forced args)))
                               (case cse [(\l r -> r)])) ])
                     , (forced (case cse [(\l r -> r)])) ])
                , (forced (case cse [(\l r -> r)])) ])
             (unConstrData d)) ]))
(program
   1.1.0
   (\d ->
      case
        ((\tup -> constr 0 [(case tup [(\l r -> l)]), (case tup [(\l r -> r)])])
           (unConstrData d))
        [ (\ds
            ds ->
             case
               (equalsInteger 0 ds)
               [ (case
                    ((\tup ->
                        constr 0
                          [(case tup [(\l r -> l)]), (case tup [(\l r -> r)])])
                       (unConstrData d))
                    [ (\ds
                        ds ->
                         case
                           (equalsInteger 1 ds)
                           [ (case
                                ((\tup ->
                                    constr 0
                                      [ (case tup [(\l r -> l)])
                                      , (case tup [(\l r -> r)]) ])
                                   (unConstrData d))
                                [ (\ds
                                    ds ->
                                     case
                                       (equalsInteger 2 ds)
                                       [ ((\cse -> case cse [cse]) error)
                                       , ((\ds ->
                                             (\ds ->
                                                (\`$mInts` ->
                                                   `$mInts`
                                                     ds
                                                     (\x
                                                       y
                                                       z
                                                       w ->
                                                        `$mInts`
                                                          (force headList ds)
                                                          (\x
                                                            y
                                                            z
                                                            w ->
                                                             constrData
                                                               0
                                                               (force
                                                                  mkCons
                                                                  (iData
                                                                     (addInteger
                                                                        x
                                                                        x))
                                                                  (force
                                                                     mkCons
                                                                     (iData
                                                                        (addInteger
                                                                           y
                                                                           y))
                                                                     (force
                                                                        mkCons
                                                                        (iData
                                                                           (addInteger
                                                                              z
                                                                              z))
                                                                        (force
                                                                           mkCons
                                                                           (iData
                                                                              (addInteger
                                                                                 w
                                                                                 w))
                                                                           [  ])))))
                                                          (\void ->
                                                             (\cse ->
                                                                case cse [cse])
                                                               error)))
                                                  (\scrut
                                                    cont
                                                    fail ->
                                                     case
                                                       ((\l ->
                                                           constr 0
                                                             [ (force headList
                                                                  l)
                                                             , (force tailList
                                                                  l) ])
                                                          (case
                                                             (unConstrData
                                                                scrut)
                                                             [(\l r -> r)]))
                                                       [ (\ds
                                                           ds ->
                                                            (\ds ->
                                                               (\ds ->
                                                                  (\ds ->
                                                                     (\ds ->
                                                                        cont
                                                                          (unIData
                                                                             ds)
                                                                          (unIData
                                                                             ds)
                                                                          (unIData
                                                                             ds)
                                                                          (unIData
                                                                             (force
                                                                                headList
                                                                                ds)))
                                                                       (force
                                                                          tailList
                                                                          ds))
                                                                    (force
                                                                       headList
                                                                       ds))
                                                                 (force tailList
                                                                    ds))
                                                              (force headList
                                                                 ds)) ])
                                                  (\void ->
                                                     (\cse -> case cse [cse])
                                                       error))
                                               (force tailList ds))
                                            (force headList ds)) ]) ])
                           , (force headList ds) ]) ])
               , (force headList ds) ]) ]))
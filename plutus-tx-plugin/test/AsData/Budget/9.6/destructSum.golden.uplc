(program
   1.1.0
   ((\forced forced d ->
       case
         (unConstrData d)
         [ (\idx args ->
              case
                idx
                [ (forced args)
                , (forced args)
                , (case
                     args
                     [ (\hd tl ->
                          (\`$mInts` ->
                             case
                               (constr 0
                                  [ hd
                                  , (\x y z w ->
                                       case
                                         (constr 0
                                            [ (forced tl)
                                            , (\x y z w ->
                                                 constrData
                                                   0
                                                   (forced
                                                      (iData (addInteger x x))
                                                      (forced
                                                         (iData
                                                            (addInteger y y))
                                                         (forced
                                                            (iData
                                                               (addInteger z z))
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
                                  , (\void -> (\cse -> case cse [cse]) error) ])
                               [`$mInts`])
                            (\scrut cont fail ->
                               case
                                 (case (unConstrData scrut) [(\l r -> r)])
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
                                                         , (unIData
                                                              (forced ds)) ])
                                                      [cont]) ]) ]) ])) ]) ]) ])
      (force mkCons)
      (force headList)))
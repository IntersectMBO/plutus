(program
   1.1.0
   ((\cse ->
       (\cse ->
          case
            (unConstrData
               (constrData
                  1
                  (cse
                     (cse
                        (cse
                           (cse
                              (cse
                                 (Constr 1 [])
                                 (cse (iData 1) (cse (Constr 0 []) []))))
                           []))
                     [])))
            [ (\index
                args ->
                 case
                   index
                   [ (\ds -> constr 0 [(unIData (force headList ds))])
                   , (\ds ->
                        (\cse ->
                           constr 1
                             [ (case
                                  (unConstrData (cse ds))
                                  [ (\index
                                      args ->
                                       case
                                         index
                                         [ (\ds ->
                                              constr 0
                                                [ (case
                                                     (unConstrData (cse ds))
                                                     [ (\index
                                                         args ->
                                                          case
                                                            index
                                                            [ (\ds ->
                                                                 (\cse ->
                                                                    (\cse ->
                                                                       constr 0
                                                                         [ (case
                                                                              (unConstrData
                                                                                 (cse
                                                                                    ds))
                                                                              [ (\index
                                                                                  args ->
                                                                                   case
                                                                                     index
                                                                                     [ (\ds ->
                                                                                          False)
                                                                                     , (\ds ->
                                                                                          True) ]
                                                                                     args) ])
                                                                         , (unIData
                                                                              (cse
                                                                                 cse))
                                                                         , (case
                                                                              (unConstrData
                                                                                 (cse
                                                                                    (cse
                                                                                       cse)))
                                                                              [ (\index
                                                                                  args ->
                                                                                   case
                                                                                     index
                                                                                     [ (\ds ->
                                                                                          False)
                                                                                     , (\ds ->
                                                                                          True) ]
                                                                                     args) ]) ])
                                                                      (cse ds))
                                                                   (force
                                                                      tailList)) ]
                                                            args) ]) ])
                                         , (\ds -> constr 1 []) ]
                                         args) ]) ])
                          (force headList)) ]
                   args) ])
         (force mkCons))
      (constrData 0)))
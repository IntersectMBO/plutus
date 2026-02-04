(program
   1.1.0
   (case
      (unConstrData
         (constrData
            1
            (force mkCons
               (constrData
                  0
                  (force mkCons
                     (constrData
                        0
                        (force mkCons
                           (Constr 1 [])
                           (force mkCons
                              (iData 1)
                              (force mkCons (Constr 0 []) []))))
                     []))
               [])))
      [ (\index
          args ->
           case
             index
             [ (\ds -> constr 0 [(unIData (force headList ds))])
             , (\ds ->
                  constr 1
                    [ (case
                         (unConstrData (force headList ds))
                         [ (\index
                             args ->
                              case
                                index
                                [ (\ds ->
                                     constr 0
                                       [ (case
                                            (unConstrData (force headList ds))
                                            [ (\index
                                                args ->
                                                 case
                                                   index
                                                   [ (\ds ->
                                                        (\l ->
                                                           constr 0
                                                             [ (case
                                                                  (unConstrData
                                                                     (force
                                                                        headList
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
                                                                  (force
                                                                     headList
                                                                     l))
                                                             , (case
                                                                  (unConstrData
                                                                     (force
                                                                        headList
                                                                        (force
                                                                           tailList
                                                                           l)))
                                                                  [ (\index
                                                                      args ->
                                                                       case
                                                                         index
                                                                         [ (\ds ->
                                                                              False)
                                                                         , (\ds ->
                                                                              True) ]
                                                                         args) ]) ])
                                                          (force tailList ds)) ]
                                                   args) ]) ])
                                , (\ds -> constr 1 []) ]
                                args) ]) ]) ]
             args) ]))
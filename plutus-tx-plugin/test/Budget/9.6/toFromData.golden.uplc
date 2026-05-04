(program
   1.1.0
   (constr 1
      [ (constr 0
           [ (constr 0
                [ (case
                     (1, [])
                     [ (\index args ->
                          case index [(\ds -> False), (\ds -> True)] args) ])
                , (unIData (force headList [I 1, Constr 0 []]))
                , (case
                     (unConstrData
                        (force headList (force tailList [I 1, Constr 0 []])))
                     [ (\index args ->
                          case index [(\ds -> False), (\ds -> True)]
                            args) ]) ]) ]) ]))
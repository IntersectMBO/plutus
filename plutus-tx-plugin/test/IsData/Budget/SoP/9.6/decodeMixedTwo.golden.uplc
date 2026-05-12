(program
   1.1.0
   ((\forced
      forced
      forced
      forced
      forced
      d ->
       (\p ->
          (\index ->
             (\args ->
                case
                  (force
                     (case
                        (constr 0
                           [ (equalsInteger 0 index)
                           , (delay (\ds -> constr 0 []))
                           , (delay
                                (force
                                   (case
                                      (constr 0
                                         [ (equalsInteger 1 index)
                                         , (delay
                                              (\ds ->
                                                 constr 1
                                                   [(unIData (forced ds))]))
                                         , (delay
                                              (force
                                                 (case
                                                    (constr 0
                                                       [ (equalsInteger 2 index)
                                                       , (delay
                                                            (\ds ->
                                                               constr 2
                                                                 [ (unIData
                                                                      (forced
                                                                         ds))
                                                                 , (unIData
                                                                      (forced
                                                                         (forced
                                                                            ds))) ]))
                                                       , (delay error) ])
                                                    [forced]))) ])
                                      [forced]))) ])
                        [forced])
                     args)
                  [0, (\x -> x), (\x y -> addInteger x y)])
               (forced p))
            (forced p))
         (unConstrData d))
      (force (force fstPair))
      (force tailList)
      (force ifThenElse)
      (force (force sndPair))
      (force headList)))
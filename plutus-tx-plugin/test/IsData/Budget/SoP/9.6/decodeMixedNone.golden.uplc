(program
   1.1.0
   (\d ->
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
                                                  [ (unIData
                                                       (force headList ds)) ]))
                                        , (delay
                                             (force
                                                (case
                                                   (constr 0
                                                      [ (equalsInteger 2 index)
                                                      , (delay
                                                           (\ds ->
                                                              constr 2
                                                                [ (unIData
                                                                     (force
                                                                        headList
                                                                        ds))
                                                                , (unIData
                                                                     (force
                                                                        headList
                                                                        (force
                                                                           tailList
                                                                           ds))) ]))
                                                      , (delay error) ])
                                                   [(force ifThenElse)]))) ])
                                     [(force ifThenElse)]))) ])
                       [(force ifThenElse)])
                    args)
                 [0, (\x -> x), (\x y -> addInteger x y)])
              (force (force sndPair) p))
           (force (force fstPair) p))
        (unConstrData d)))
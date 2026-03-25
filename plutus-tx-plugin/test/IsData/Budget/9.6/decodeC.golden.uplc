(program
   1.1.0
   (\d ->
      case
        ((\traceError ->
            (\p ->
               (\index args ->
                  (\go ->
                     force
                       (case
                          (constr 0
                             [ (lessThanInteger index 0)
                             , (delay (traceError "PT6"))
                             , (delay
                                  (force go
                                     index
                                     (constr 1
                                        [ (\ds ->
                                             constr 0
                                               [(unIData (force headList ds))])
                                        , (constr 1
                                             [ (\ds ->
                                                  constr 1
                                                    [ (unIData
                                                         (force headList ds)) ])
                                             , (constr 1
                                                  [ (\ds ->
                                                       constr 2
                                                         [ (unIData
                                                              (force headList
                                                                 ds)) ])
                                                  , (constr 0 []) ]) ]) ]))) ])
                          [(force ifThenElse)]))
                    ((\f ->
                        (\s ->
                           f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
                          (\s -> f (\x -> s s x)))
                       (\go arg ->
                          delay
                            (\ds ds ->
                               case
                                 ds
                                 [ (traceError "PT7")
                                 , (\x xs ->
                                      force
                                        (case
                                           (constr 0
                                              [ (equalsInteger ds 0)
                                              , (delay x)
                                              , (delay
                                                   (force (go (delay (\x -> x)))
                                                      (subtractInteger ds 1)
                                                      xs)) ])
                                           [(force ifThenElse)])) ]))
                       (delay (\x -> x)))
                    args)
                 (force (force fstPair) p)
                 (force (force sndPair) p))
              (unConstrData d))
           (\str -> (\x -> error) (force trace str (constr 0 []))))
        [(\x -> x), (\x -> addInteger x 100), (\x -> addInteger x 200)]))
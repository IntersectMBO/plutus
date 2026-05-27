(program
   1.1.0
   (case
      (constr 0
         [ (force (force fstPair))
         , (force tailList)
         , (force ifThenElse)
         , (force (force sndPair))
         , (force headList)
         , (force (force chooseList)) ])
      [ (\forced
          forced
          forced
          forced
          forced
          forced ->
           (\caseList' ->
              (\goInner
                bd ->
                 (\ds ->
                    (\s ->
                       s s ds)
                      (\s ->
                         caseList'
                           0
                           (\hd ->
                              case
                                (constr 0
                                   [ (equalsByteString
                                        #706f6c6963795f30315f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                                        (unBData (forced hd)))
                                   , (\ds ->
                                        force goInner (unMapData (forced hd)))
                                   , (\x -> s s x) ])
                                [forced])))
                   (unMapData bd))
                ((\s ->
                    s s (delay (\x -> x)))
                   (\s
                     arg ->
                      delay
                        (caseList'
                           0
                           (\hd ->
                              force
                                (case
                                   (constr 0
                                      [ (equalsByteString
                                           #746f6b656e5f30315f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                                           (unBData (forced hd)))
                                      , (delay (\ds -> unIData (forced hd)))
                                      , (delay
                                           (force (s s (delay (\x -> x))))) ])
                                   [forced]))))))
             (\z f xs ->
                force
                  (case
                     (constr 0
                        [xs, (delay z), (delay (f (forced xs) (forced xs)))])
                     [forced]))) ]))
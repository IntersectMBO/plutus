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
          forced
          bd ->
           (\s ->
              s s (unMapData bd))
             (\s ->
                (\cse ->
                   cse
                     (\hd ->
                        case
                          (constr 0
                             [ (equalsByteString
                                  #706f6c6963795f30355f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                                  (unBData (forced hd)))
                             , (\ds ->
                                  (\s ->
                                     s s (unMapData (forced hd)))
                                    (\s ->
                                       cse
                                         (\hd ->
                                            case
                                              (constr 0
                                                 [ (equalsByteString
                                                      #746f6b656e5f30355f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                                                      (unBData (forced hd)))
                                                 , (\ds -> unIData (forced hd))
                                                 , (\x -> s s x) ])
                                              [forced])))
                             , (\x -> s s x) ])
                          [forced]))
                  (\f xs ->
                     force
                       (case
                          (constr 0
                             [ xs
                             , (delay 0)
                             , (delay (f (forced xs) (forced xs))) ])
                          [forced])))) ]))
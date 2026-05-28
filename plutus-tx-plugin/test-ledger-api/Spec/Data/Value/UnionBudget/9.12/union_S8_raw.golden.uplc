(program
   1.1.0
   (case
      (constr 0
         [ (force (force fstPair))
         , (force mkCons)
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
          forced ->
           (\caseList' ->
              (\go ->
                 (\go bd bd ->
                    mapData (go (unMapData bd) (unMapData bd)))
                   ((\s ->
                       s s)
                      (\s
                        lA
                        lB ->
                         case
                           (constr 0
                              [ lB
                              , (\hdA
                                  tlA ->
                                   case
                                     (constr 0
                                        [ lA
                                        , (\hdB
                                            tlB ->
                                             (\keyB ->
                                                (\cse ->
                                                   (\keyA ->
                                                      force
                                                        (case
                                                           (constr 0
                                                              [ (equalsByteString
                                                                   keyA
                                                                   keyB)
                                                              , (delay
                                                                   (forced
                                                                      (mkPairData
                                                                         cse
                                                                         (mapData
                                                                            (go
                                                                               (unMapData
                                                                                  (forced
                                                                                     hdA))
                                                                               (unMapData
                                                                                  (forced
                                                                                     hdB)))))
                                                                      (case
                                                                         (constr 0
                                                                            [ s
                                                                            , tlA
                                                                            , tlB ])
                                                                         [s])))
                                                              , (delay
                                                                   (force
                                                                      (case
                                                                         (constr 0
                                                                            [ (lessThanByteString
                                                                                 keyA
                                                                                 keyB)
                                                                            , (delay
                                                                                 (forced
                                                                                    hdA
                                                                                    (case
                                                                                       (constr 0
                                                                                          [ s
                                                                                          , tlA
                                                                                          , lB ])
                                                                                       [ s ])))
                                                                            , (delay
                                                                                 (forced
                                                                                    hdB
                                                                                    (case
                                                                                       (constr 0
                                                                                          [ s
                                                                                          , lA
                                                                                          , tlB ])
                                                                                       [ s ]))) ])
                                                                         [ forced ]))) ])
                                                           [forced]))
                                                     (unBData cse))
                                                  (forced hdA))
                                               (unBData (forced hdB)))
                                        , lB ])
                                     [caseList'])
                              , lA ])
                           [caseList'])))
                ((\s ->
                    s s)
                   (\s
                     lA
                     lB ->
                      case
                        (constr 0
                           [ lB
                           , (\hdA
                               tlA ->
                                case
                                  (constr 0
                                     [ lA
                                     , (\hdB
                                         tlB ->
                                          (\keyB ->
                                             (\cse ->
                                                (\keyA ->
                                                   force
                                                     (case
                                                        (constr 0
                                                           [ (equalsByteString
                                                                keyA
                                                                keyB)
                                                           , (delay
                                                                (forced
                                                                   (mkPairData
                                                                      cse
                                                                      (iData
                                                                         (addInteger
                                                                            (unIData
                                                                               (forced
                                                                                  hdA))
                                                                            (unIData
                                                                               (forced
                                                                                  hdB)))))
                                                                   (case
                                                                      (constr 0
                                                                         [ s
                                                                         , tlA
                                                                         , tlB ])
                                                                      [s])))
                                                           , (delay
                                                                (force
                                                                   (case
                                                                      (constr 0
                                                                         [ (lessThanByteString
                                                                              keyA
                                                                              keyB)
                                                                         , (delay
                                                                              (forced
                                                                                 hdA
                                                                                 (case
                                                                                    (constr 0
                                                                                       [ s
                                                                                       , tlA
                                                                                       , lB ])
                                                                                    [ s ])))
                                                                         , (delay
                                                                              (forced
                                                                                 hdB
                                                                                 (case
                                                                                    (constr 0
                                                                                       [ s
                                                                                       , lA
                                                                                       , tlB ])
                                                                                    [ s ]))) ])
                                                                      [ forced ]))) ])
                                                        [forced]))
                                                  (unBData cse))
                                               (forced hdA))
                                            (unBData (forced hdB)))
                                     , lB ])
                                  [caseList'])
                           , lA ])
                        [caseList'])))
             (\z f xs ->
                force
                  (case
                     (constr 0
                        [xs, (delay z), (delay (f (forced xs) (forced xs)))])
                     [forced]))) ]))
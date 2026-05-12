(program
   1.1.0
   (case
      (constr 0 [(force tailList), (force headList), (force trace)])
      [ (\forced forced forced obsScriptCred ctx ->
           (\ds ->
              (\wdrlAtZero ->
                 (\rest ->
                    (\wdrlAtOne ->
                       case
                         (equalsData obsScriptCred wdrlAtZero)
                         [ (case
                              (equalsData obsScriptCred wdrlAtOne)
                              [ ((\s ->
                                    case
                                      (s s rest)
                                      [ ((\x -> error)
                                           (forced "not found" (constr 0 [])))
                                      , (constr 0 []) ])
                                   (\s xs ->
                                      case
                                        xs
                                        [ (\x xs ->
                                             case
                                               (equalsData
                                                  obsScriptCred
                                                  (case x [(\l r -> l)]))
                                               [(s s xs), True])
                                        , False ]))
                              , (constr 0 []) ])
                         , (constr 0 []) ])
                      (case (forced rest) [(\l r -> l)]))
                   (forced ds))
                (case (forced ds) [(\l r -> l)]))
             (unMapData
                (forced
                   (forced
                      (forced
                         (forced
                            (forced
                               (forced
                                  (forced
                                     (case
                                        (unConstrData
                                           (forced
                                              (case
                                                 (unConstrData ctx)
                                                 [(\l r -> r)])))
                                        [(\l r -> r)])))))))))) ]))
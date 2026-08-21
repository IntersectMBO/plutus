(program
   1.1.0
   (case
      (constr 0
         [(force tailList), (force headList), (force trace), (force dropList)])
      [ (\forced forced forced forced obsScriptCred ctx ->
           case
             (case (unConstrData ctx) [(\l r -> r)])
             [ (\ds ds ->
                  case
                    (forced 6 (case (unConstrData ds) [(\l r -> r)]))
                    [ (\ds ds ->
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
                                                         (forced
                                                            "not found"
                                                            ()))
                                                    , () ])
                                                 (\s xs ->
                                                    case
                                                      xs
                                                      [ (\x xs ->
                                                           case
                                                             (equalsData
                                                                obsScriptCred
                                                                (case
                                                                   x
                                                                   [ (\l r ->
                                                                        l) ]))
                                                             [(s s xs), True])
                                                      , False ]))
                                            , () ])
                                       , () ])
                                    (case (forced rest) [(\l r -> l)]))
                                 (forced ds))
                              (case (forced ds) [(\l r -> l)]))
                           (unMapData ds)) ]) ]) ]))
(program
   1.1.0
   (\obsScriptCred ctx ->
      (\ds ->
         (\wdrlAtZero ->
            (\rest ->
               (\wdrlAtOne ->
                  case
                    (equalsData obsScriptCred wdrlAtZero)
                    [ (case
                         (equalsData obsScriptCred wdrlAtOne)
                         [ (case
                              ((\s -> s s)
                                 (\s xs ->
                                    case
                                      xs
                                      [ (\x xs ->
                                           case
                                             (equalsData
                                                obsScriptCred
                                                (case x [(\l r -> l)]))
                                             [(s s xs), True])
                                      , False ])
                                 rest)
                              [ ((\x -> error)
                                   (force trace "not found" (constr 0 [])))
                              , (constr 0 []) ])
                         , (constr 0 []) ])
                    , (constr 0 []) ])
                 (case (force headList rest) [(\l r -> l)]))
              (force tailList ds))
           (case (force headList ds) [(\l r -> l)]))
        (unMapData
           (force headList
              (force tailList
                 (force tailList
                    (force tailList
                       (force tailList
                          (force tailList
                             (force tailList
                                (case
                                   (unConstrData
                                      (force headList
                                         (case
                                            (unConstrData ctx)
                                            [(\l r -> r)])))
                                   [(\l r -> r)])))))))))))
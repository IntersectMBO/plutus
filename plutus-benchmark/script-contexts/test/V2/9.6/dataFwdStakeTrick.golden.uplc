(program
   1.1.0
   (\obsScriptCred ctx ->
      (\cse ->
         (\cse ->
            (\cse ->
               (\wdrlAtZero ->
                  (\cse ->
                     (\wdrlAtOne ->
                        (\cse ->
                           case
                             (cse wdrlAtZero)
                             [ (case
                                  (cse wdrlAtOne)
                                  [ (case
                                       ((\cse -> cse cse)
                                          (\s xs ->
                                             case
                                               xs
                                               [ (\x xs ->
                                                    case
                                                      (cse
                                                         (case x [(\l r -> l)]))
                                                      [(s s xs), True])
                                               , False ])
                                          cse)
                                       [ ((\x -> error)
                                            (force trace
                                               "not found"
                                               (constr 0 [])))
                                       , (constr 0 []) ])
                                  , (constr 0 []) ])
                             , (constr 0 []) ])
                          (equalsData obsScriptCred))
                       (case (cse cse) [(\l r -> l)]))
                    (cse cse))
                 (case (cse cse) [(\l r -> l)]))
              (unMapData
                 (cse
                    (cse
                       (cse
                          (cse
                             (cse
                                (cse
                                   (cse
                                      (case
                                         (unConstrData
                                            (cse
                                               (case
                                                  (unConstrData ctx)
                                                  [(\l r -> r)])))
                                         [(\l r -> r)]))))))))))
           (force tailList))
        (force headList)))
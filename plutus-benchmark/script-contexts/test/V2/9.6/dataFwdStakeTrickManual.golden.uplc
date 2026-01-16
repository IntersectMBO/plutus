(program
   1.1.0
   (\r_stake_cred ->
      (\lookForCred r_ctx ->
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
                                     [(lookForCred cse), (constr 0 [])])
                                , (constr 0 []) ])
                             (equalsData r_stake_cred))
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
                                                     (unConstrData r_ctx)
                                                     [(\l r -> r)])))
                                            [(\l r -> r)]))))))))))
              (force headList))
           (force tailList))
        ((\cse -> cse cse)
           (\s l ->
              case
                l
                [ (\x xs ds ->
                     case
                       (equalsData r_stake_cred (case x [(\l r -> l)]))
                       [(s s xs), (constr 0 [])])
                , (\ds ->
                     (\x -> error) (force trace "not found" (constr 0 []))) ]
                (constr 0 [])))))
(program
   1.1.0
   (\r_stake_cred ->
      (\lookForCred r_ctx ->
         (\wdrl ->
            (\wdrlAtZero ->
               (\rest ->
                  (\wdrlAtOne ->
                     case
                       (equalsData r_stake_cred wdrlAtZero)
                       [ (case
                            (equalsData r_stake_cred wdrlAtOne)
                            [(lookForCred rest), (constr 0 [])])
                       , (constr 0 []) ])
                    (case (force headList rest) [(\l r -> l)]))
                 (force tailList wdrl))
              (case (force headList wdrl) [(\l r -> l)]))
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
                                               (unConstrData r_ctx)
                                               [(\l r -> r)])))
                                      [(\l r -> r)]))))))))))
        ((\s -> s s)
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
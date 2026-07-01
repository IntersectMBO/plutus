(program
   1.1.0
   (case
      (constr 0 [(force tailList), (force headList), (force trace)])
      [ (\forced forced forced r_stake_cred ->
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
                         (case (forced rest) [(\l r -> l)]))
                      (forced wdrl))
                   (case (forced wdrl) [(\l r -> l)]))
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
                          (\x -> error) (forced "not found" (constr 0 []))) ]
                     (constr 0 [])))) ]))
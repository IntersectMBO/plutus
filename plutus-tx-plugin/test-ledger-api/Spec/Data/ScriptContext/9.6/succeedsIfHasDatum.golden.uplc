(program
   1.1.0
   (case
      (constr 0 [(force headList), (force trace), (force dropList)])
      [ (\forced forced forced d ->
           (\tup ->
              case
                (case
                   (equalsInteger 1 (case tup [(\l r -> l)]))
                   [ False
                   , (case
                        (case tup [(\l r -> r)])
                        [ (\ds ds ->
                             case
                               (case
                                  (unConstrData (forced ds))
                                  [ (\index args ->
                                       case
                                         index
                                         [ (\ds -> constr 0 [(forced ds)])
                                         , (\ds -> constr 1 []) ]
                                         args) ])
                               [(\ds -> True), False]) ]) ])
                [((\x -> error) (forced "PT5" ())), ()])
             (unConstrData
                (forced (forced 2 (case (unConstrData d) [(\l r -> r)]))))) ]))
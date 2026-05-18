(program
   1.1.0
   (case
      (constr 0 [(force tailList), (force headList), (force trace)])
      [ (\forced forced forced d ->
           (\tup ->
              case
                (case
                   (equalsInteger 1 (case tup [(\l r -> l)]))
                   [ False
                   , (case
                        (case
                           (unConstrData
                              (forced (forced (case tup [(\l r -> r)]))))
                           [ (\index args ->
                                case
                                  index
                                  [ (\ds -> constr 0 [(forced ds)])
                                  , (\ds -> constr 1 []) ]
                                  args) ])
                        [(\ds -> True), False]) ])
                [((\x -> error) (forced "PT5" (constr 0 []))), ()])
             (unConstrData
                (forced
                   (forced
                      (forced (case (unConstrData d) [(\l r -> r)])))))) ]))
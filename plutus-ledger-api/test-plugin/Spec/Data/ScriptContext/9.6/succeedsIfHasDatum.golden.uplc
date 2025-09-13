(program
   1.1.0
   (\d ->
      case
        ((\tup ->
            case
              (equalsInteger 1 (case tup [(\l r -> l)]))
              [ False
              , (case
                   (case
                      (unConstrData
                         (force headList
                            (force tailList (case tup [(\l r -> r)]))))
                      [ (\index args ->
                           case
                             index
                             [ (\ds -> constr 0 [(force headList ds)])
                             , (\ds -> constr 1 []) ]
                             args) ])
                   [(\ds -> True), False]) ])
           (unConstrData
              (force headList
                 (force tailList
                    (force tailList (case (unConstrData d) [(\l r -> r)]))))))
        [((\x -> error) (force trace "PT5" (constr 0 []))), ()]))
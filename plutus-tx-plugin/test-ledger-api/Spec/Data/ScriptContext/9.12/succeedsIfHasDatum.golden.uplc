(program
   1.1.0
   ((\forced forced d ->
       case
         (case
            (case (unConstrData d) [(\l r -> r)])
            [ (\ds ds ->
                 case
                   ds
                   [ (\ds ds ->
                        (\tup ->
                           case
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
                                                   [ (\ds ->
                                                        constr 0 [(forced ds)])
                                                   , (\ds -> constr 1 []) ]
                                                   args) ])
                                         [(\ds -> True), False]) ]) ])
                          (unConstrData (forced ds))) ]) ])
         [((\x -> error) (forced "PT5" (constr 0 []))), ()])
      (force headList)
      (force trace)))
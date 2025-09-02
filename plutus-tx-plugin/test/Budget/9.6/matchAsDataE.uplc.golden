(program
   1.1.0
   ((\ds ->
       case
         ((\tup ->
             constr 0 [(case tup [(\l r -> l)]), (case tup [(\l r -> r)])])
            (unConstrData ds))
         [ (\ds ds ->
              case
                (equalsInteger 0 ds)
                [ (case
                     ((\tup ->
                         constr 0
                           [(case tup [(\l r -> l)]), (case tup [(\l r -> r)])])
                        (unConstrData ds))
                     [ (\ds ds ->
                          case
                            (equalsInteger 1 ds)
                            [((\cse -> case cse [cse]) error), 1]) ])
                , (unIData (force headList ds)) ]) ])
      (Constr 0 [I 1])))
(program
   1.1.0
   ((\ds ->
       case
         ((\cse ->
             constr 0 [(case cse [(\l r -> l)]), (case cse [(\l r -> r)])])
            (unConstrData ds))
         [ (\ds ds ->
              case
                (equalsInteger 0 ds)
                [ (case
                     ((\cse ->
                         constr 0
                           [(case cse [(\l r -> l)]), (case cse [(\l r -> r)])])
                        (unConstrData ds))
                     [ (\ds ds ->
                          case
                            (equalsInteger 1 ds)
                            [(case error [error]), 1]) ])
                , (unIData (force headList ds)) ]) ])
      (Constr 0 [I 1])))
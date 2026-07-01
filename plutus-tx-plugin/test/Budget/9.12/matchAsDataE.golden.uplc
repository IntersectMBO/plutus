(program
   1.1.0
   ((\forced ds ->
       (\cse ->
          (\ds ->
             case
               (equalsInteger 0 (case cse [(\l r -> l)]))
               [ ((\ds ->
                     case
                       (equalsInteger 1 (case cse [(\l r -> l)]))
                       [((\cse -> case cse [cse]) error), 1])
                    (case cse [(\l r -> r)]))
               , (unIData (forced ds)) ])
            (case cse [(\l r -> r)]))
         (unConstrData ds))
      (force headList)
      (Constr 0 [I 1])))
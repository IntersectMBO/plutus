(program
   1.1.0
   ((\ds ->
       (\cse ->
          (\ds ->
             case
               (equalsInteger 0 (case cse [(\l r -> l)]))
               [ ((\ds ->
                     case
                       (equalsInteger 1 (case cse [(\l r -> l)]))
                       [((\cse -> case cse [cse]) error), 1])
                    (case cse [(\l r -> r)]))
               , (unIData (force headList ds)) ])
            (case cse [(\l r -> r)]))
         (unConstrData ds))
      (Constr 0 [I 1])))
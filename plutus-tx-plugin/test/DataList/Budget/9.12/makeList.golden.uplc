(program
   1.1.0
   (\x y z ->
      (\cons ->
         case
           (constr 0
              [ (\i -> iData i)
              , x
              , (case
                   (constr 0 [(\i -> iData i), y, (force mkCons (iData z) [])])
                   [cons]) ])
           [cons])
        (\`$dToData` h eta -> force mkCons (`$dToData` h) eta)))
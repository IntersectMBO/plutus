(program
   1.1.0
   ((\forced x y z ->
       (\cons ->
          case
            (constr 0
               [ (\i -> iData i)
               , x
               , (case
                    (constr 0 [(\i -> iData i), y, (forced (iData z) [])])
                    [cons]) ])
            [cons])
         (\`$dToData` h eta -> forced (`$dToData` h) eta))
      (force mkCons)))
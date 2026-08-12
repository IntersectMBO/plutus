(program
   1.1.0
   ((\forced d ->
       case
         (forced 3 (case (unConstrData d) [(\l r -> r)]))
         [ (\ds ds ->
              case
                (forced 3 ds)
                [ (\ds ds ->
                     case
                       (forced 6 ds)
                       [ (\ds ds ->
                            addInteger
                              (unIData ds)
                              (addInteger (unIData ds) (unIData ds))) ]) ]) ])
      (force dropList)))
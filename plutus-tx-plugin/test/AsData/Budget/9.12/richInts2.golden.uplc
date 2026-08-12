(program
   1.1.0
   ((\forced d ->
       case
         (forced 8 (case (unConstrData d) [(\l r -> r)]))
         [ (\ds ds ->
              case
                (forced 4 ds)
                [(\ds ds -> addInteger (unIData ds) (unIData ds))]) ])
      (force dropList)))
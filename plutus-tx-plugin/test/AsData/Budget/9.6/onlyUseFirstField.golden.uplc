(program
   1.1.0
   (\d ->
      case
        ((\l -> constr 0 [(force headList l), (force tailList l)])
           (case (unConstrData d) [(\l r -> r)]))
        [ (\ds ds ->
             (\ds ->
                (\ds ->
                   (\ds -> (\ds -> unIData ds) (force tailList ds))
                     (force headList ds))
                  (force tailList ds))
               (force headList ds)) ]))
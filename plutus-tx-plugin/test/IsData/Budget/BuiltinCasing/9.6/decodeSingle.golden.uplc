(program
   1.1.0
   (\d ->
      case
        (case
           (unConstrData d)
           [ (\index args ->
                case index [(\ds -> constr 0 [(unIData (force headList ds))])]
                  args) ])
        [(\x -> x)]))
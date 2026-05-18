(program
   1.1.0
   ((\forced d ->
       case
         (case
            (unConstrData d)
            [ (\index args ->
                 case index [(\ds -> constr 0 [(unIData (forced ds))])] args) ])
         [(\x -> x)])
      (force headList)))
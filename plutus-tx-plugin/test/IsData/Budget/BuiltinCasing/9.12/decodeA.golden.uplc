(program
   1.1.0
   ((\forced d ->
       case
         (case
            (unConstrData d)
            [ (\index args ->
                 case
                   index
                   [ (\ds -> constr 0 [(unIData (forced ds))])
                   , (\ds -> constr 1 [(unIData (forced ds))])
                   , (\ds -> constr 2 [(unIData (forced ds))]) ]
                   args) ])
         [(\x -> x), (\x -> addInteger 100 x), (\x -> addInteger 200 x)])
      (force headList)))
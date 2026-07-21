(program
   1.1.0
   ((\forced forced d ->
       case
         (case
            (unConstrData d)
            [ (\index args ->
                 case
                   index
                   [ (\ds -> constr 0 [])
                   , (\ds -> constr 1 [(unIData (forced ds))])
                   , (\ds ->
                        constr 2
                          [ (unIData (forced ds))
                          , (unIData (forced (forced ds))) ]) ]
                   args) ])
         [0, (\x -> x), (\x y -> addInteger x y)])
      (force tailList)
      (force headList)))
(program
   1.1.0
   ((\forced d ->
       case
         (case
            (unConstrData d)
            [ (\index args ->
                 case
                   index
                   [ (\ds -> constr 0 [])
                   , (\ds -> constr 1 [(unIData (forced ds))])
                   , (\ds ->
                        case
                          ds
                          [ (\ds ds ->
                               constr 2
                                 [(unIData ds), (unIData (forced ds))]) ]) ]
                   args) ])
         [0, (\x -> x), (\x y -> addInteger x y)])
      (force headList)))
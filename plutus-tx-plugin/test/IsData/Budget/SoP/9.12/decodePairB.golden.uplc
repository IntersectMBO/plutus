(program
   1.1.0
   ((\forced d ->
       case
         (case
            d
            [ (\ds -> constr 0 [(unIData (forced ds))])
            , (\ds -> constr 1 [(unIData (forced ds))]) ])
         [(\x -> x), (\x -> addInteger 1 x)])
      (force headList)))
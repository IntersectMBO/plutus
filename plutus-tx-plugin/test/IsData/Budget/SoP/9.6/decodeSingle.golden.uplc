(program
   1.1.0
   ((\forced d ->
       case (case d [(\ds -> constr 0 [(unIData (forced ds))])]) [(\x -> x)])
      (force headList)))
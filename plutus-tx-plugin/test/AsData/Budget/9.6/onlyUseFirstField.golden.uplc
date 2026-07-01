(program
   1.1.0
   ((\forced d -> unIData (forced (case (unConstrData d) [(\l r -> r)])))
      (force headList)))
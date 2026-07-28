(program
   1.1.0
   ((\forced forced d ->
       unIData (forced (forced 15 (case (unConstrData d) [(\l r -> r)]))))
      (force headList)
      (force dropList)))
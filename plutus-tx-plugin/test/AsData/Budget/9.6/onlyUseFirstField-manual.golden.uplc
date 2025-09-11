(program
   1.1.0
   (\d -> unIData (force headList (case (unConstrData d) [(\l r -> r)]))))
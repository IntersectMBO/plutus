(program
   1.1.0
   ((\forced forced xs ->
       (\ds -> (\ds -> delay (\case_Tuple2 -> case_Tuple2 ds ds)) (forced xs))
         (forced xs))
      (force tailList)
      (force headList)))
(program
   1.1.0
   ((\forced x y z ->
       (\eta -> forced (iData x) eta)
         ((\eta -> forced (iData y) eta) (forced (iData z) [])))
      (force mkCons)))
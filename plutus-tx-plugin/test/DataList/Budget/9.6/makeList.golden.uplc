(program
   1.2.0
   ((\forced x y z ->
       (\eta -> forced (iData x) eta)
         ((\eta -> forced (iData y) eta) (forced (iData z) [])))
      (force mkCons)))
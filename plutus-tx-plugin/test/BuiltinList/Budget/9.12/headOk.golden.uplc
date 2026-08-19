(program
   1.1.0
   ((\forced xs ->
       case
         xs
         [(\x xs ds -> x), (\ds -> (\x -> error) (forced "PT23" (constr 0 [])))]
         (constr 0 []))
      (force trace)))
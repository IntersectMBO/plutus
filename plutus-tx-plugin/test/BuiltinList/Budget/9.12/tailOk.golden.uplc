(program
   1.1.0
   ((\forced xs ->
       case
         xs
         [ (\x xs ds -> xs)
         , (\ds -> (\x -> error) (forced "PT25" (constr 0 []))) ]
         (constr 0 []))
      (force trace)))
(program
   1.1.0
   ((\forced xs ->
       case xs [(\x xs ds -> x), (\ds -> (\x -> error) (forced "PT23" ()))] ())
      (force trace)))
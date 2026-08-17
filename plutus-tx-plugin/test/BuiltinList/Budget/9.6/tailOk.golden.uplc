(program
   1.1.0
   ((\forced xs ->
       case xs [(\x xs ds -> xs), (\ds -> (\x -> error) (forced "PT25" ()))] ())
      (force trace)))
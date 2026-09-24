(program
   1.2.0
   ((\forced xs ->
       case xs [(\x xs ds -> xs), (\ds -> (\x -> error) (forced "PT25" ()))] ())
      (force trace)))
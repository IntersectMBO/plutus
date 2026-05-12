(program
   1.1.0
   ((\go eta -> go eta)
      ((\s -> s s)
         (\s ds ->
            case
              ds
              [ (\x eta ->
                   case (lessThanEqualsInteger 8 (unIData x)) [(s s eta), True])
              , False ]))))
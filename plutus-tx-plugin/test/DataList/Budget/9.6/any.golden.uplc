(program
   1.1.0
   ((\go eta -> go eta)
      ((\cse -> cse cse)
         (\s ds ->
            case
              ds
              [ (\x eta ->
                   case (lessThanInteger (unIData x) 8) [True, (s s eta)])
              , False ]))))
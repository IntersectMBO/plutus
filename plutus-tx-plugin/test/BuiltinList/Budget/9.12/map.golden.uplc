(program
   1.1.0
   ((\s -> s s)
      (\s xs ->
         case xs [(\x xs -> force mkCons (addInteger 1 x) (s s xs)), []])))
(program
   1.1.0
   ((\cse -> cse cse)
      (\s xs ->
         case xs [(\x xs -> force mkCons (addInteger 1 x) (s s xs)), []])))
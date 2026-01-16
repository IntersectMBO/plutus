(program
   1.1.0
   ((\go ds -> go ds)
      ((\cse -> cse cse)
         (\s xs -> case xs [(\ds eta -> addInteger 1 (s s eta)), 0]))))
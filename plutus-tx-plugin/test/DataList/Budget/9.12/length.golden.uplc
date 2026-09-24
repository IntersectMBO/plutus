(program
   1.2.0
   ((\go ds -> go ds)
      ((\s -> s s)
         (\s xs -> case xs [(\ds eta -> addInteger 1 (s s eta)), 0]))))
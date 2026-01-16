(program
   1.1.0
   ((\cse -> cse cse)
      (\s ds -> case ds [0, (\ds xs -> addInteger 1 (s s xs))])))
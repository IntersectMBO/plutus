(program
   1.1.0
   ((\go xs -> go xs)
      ((\cse -> cse cse)
         (\s xs -> case xs [(\x xs -> case x [False, (s s xs)]), True]))))
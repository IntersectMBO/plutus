(program
   1.2.0
   ((\go xs -> go xs)
      ((\s -> s s) (\s xs -> case xs [(\x xs -> addInteger 1 (s s xs)), 0]))))
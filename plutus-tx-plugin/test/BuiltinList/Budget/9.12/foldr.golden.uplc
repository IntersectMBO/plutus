(program
   1.1.0
   ((\go xs -> go xs)
      ((\s -> s s) (\s xs -> case xs [(\x xs -> addInteger x (s s xs)), 0]))))
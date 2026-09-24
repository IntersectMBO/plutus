(program
   1.2.0
   ((\forced ->
       (\s -> s s)
         (\s xs -> case xs [(\x xs -> forced (addInteger 1 x) (s s xs)), []]))
      (force mkCons)))
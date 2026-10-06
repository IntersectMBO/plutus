(program
   1.2.0
   ((\forced xs ->
       (\s -> s s xs) (\s xs -> case xs [(\x xs -> forced x (s s xs)), xs]))
      (force mkCons)))
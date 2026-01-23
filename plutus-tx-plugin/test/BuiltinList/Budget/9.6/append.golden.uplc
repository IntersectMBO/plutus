(program
   1.1.0
   (\xs ->
      (\s -> s s)
        (\s xs -> case xs [(\x xs -> force mkCons x (s s xs)), xs])
        xs))
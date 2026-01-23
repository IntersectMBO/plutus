(program
   1.1.0
   (\xs ->
      (\cse -> cse cse)
        (\s xs -> case xs [(\x xs -> force mkCons x (s s xs)), xs])
        xs))
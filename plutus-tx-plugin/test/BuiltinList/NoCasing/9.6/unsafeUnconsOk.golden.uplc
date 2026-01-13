(program
   1.1.0
   (\xs ->
      force
        (force (force chooseList)
           xs
           (delay error)
           (delay (constr 0 [(force headList xs), (force tailList xs)])))))
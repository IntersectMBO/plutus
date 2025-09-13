\x y ->
  (\cse ->
     (\cse ->
        addInteger
          cse
          (case
             y
             [ (addInteger cse (addInteger 3 x))
             , (addInteger cse (addInteger 3 x))
             , (addInteger 4 x) ]))
       (addInteger 1 cse))
    (addInteger 2 x)
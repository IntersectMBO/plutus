\x y ->
  (\cse ->
     (\cse ->
        cse
          (case
             y
             [ (cse (addInteger 3 x))
             , (addInteger cse (addInteger 3 x))
             , (addInteger 4 x) ]))
       (addInteger (addInteger 1 cse)))
    (addInteger 2 x)
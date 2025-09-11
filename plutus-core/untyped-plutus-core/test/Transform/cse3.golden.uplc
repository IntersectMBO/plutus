\f x ->
  (\cse ->
     f (addInteger 1 (addInteger cse cse)) (addInteger 2 (addInteger cse cse)))
    (addInteger 0 x)
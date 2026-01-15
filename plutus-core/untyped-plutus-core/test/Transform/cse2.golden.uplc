force
  (force
     (case
        (constr 0
           [ (lessThanInteger 0 0)
           , (delay ((\cse -> addInteger cse cse) (addInteger 1 2)))
           , (delay (addInteger 1 2)) ])
        [ifThenElse]))
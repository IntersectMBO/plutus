force
  (force
     (case
        (constr 0 [False, (delay ((\cse -> addInteger cse cse) 3)), (delay 3)])
        [ifThenElse]))
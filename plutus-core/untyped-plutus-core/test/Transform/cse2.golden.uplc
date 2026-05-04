force
  (force
     (case
        (constr 0 [False, (delay (addInteger 3 3)), (delay 3)])
        [ifThenElse]))
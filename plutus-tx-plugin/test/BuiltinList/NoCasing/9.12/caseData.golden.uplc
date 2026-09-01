(program
   1.1.0
   (case
      (constr 0
         [(force (force fstPair)), (force ifThenElse), (force (force sndPair))])
      [ (\forced forced forced d ->
           (\dataConstr ->
              force
                (case
                   (constr 0
                      [ (equalsInteger 0 (forced dataConstr))
                      , (delay (\xs -> xs))
                      , (delay error) ])
                   [forced])
                (forced dataConstr))
             (unConstrData d)) ]))
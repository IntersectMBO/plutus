(program
   1.1.0
   ((\forced forced forced forced d ->
       (\p ->
          (\index ->
             (\args ->
                case
                  (force
                     (case
                        (constr 0
                           [ (equalsInteger 0 index)
                           , (delay (\ds -> constr 0 [(unIData (forced ds))]))
                           , (delay error) ])
                        [forced])
                     args)
                  [(\x -> x)])
               (forced p))
            (forced p))
         (unConstrData d))
      (force (force fstPair))
      (force ifThenElse)
      (force (force sndPair))
      (force headList)))
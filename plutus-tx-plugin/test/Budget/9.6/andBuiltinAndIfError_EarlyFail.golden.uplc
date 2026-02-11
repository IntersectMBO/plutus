(program
   1.1.0
   ((\x y z ->
       (\b ->
          (\b ->
             (\b ->
                (\b ->
                   case
                     (case b [(\ds -> False), (\ds -> b)] ())
                     [ (\ds ->
                          (\x -> error)
                            (force trace "conditions not met" (constr 0 [])))
                     , (\ds -> ()) ]
                     ())
                  (case b [(\ds -> False), (\ds -> b)] ()))
               (lessThanInteger z 100))
            (lessThanInteger y 100))
         (lessThanInteger x 100))
      150
      60
      70))
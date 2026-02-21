(program
   1.1.0
   ((\x y z ->
       case
         (lessThanInteger x 100)
         [ (\ds ->
              (\x -> error) (force trace "conditions not met" (constr 0 [])))
         , (\ds ->
              case
                (lessThanInteger y 100)
                [ (\ds ->
                     (\x -> error)
                       (force trace "conditions not met" (constr 0 [])))
                , (\ds ->
                     case
                       (lessThanInteger z 100)
                       [ (\ds ->
                            (\x -> error)
                              (force trace "conditions not met" (constr 0 [])))
                       , (\ds -> ()) ]
                       ()) ]
                ()) ]
         ())
      50
      60
      70))
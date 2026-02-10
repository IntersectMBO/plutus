(program
   1.1.0
   ((\x y z ->
       (\b ->
          (\b -> case b [(\ds -> False), (\ds -> b)] ())
            ((\b ->
                (\b -> case b [(\ds -> False), (\ds -> b)] ())
                  (lessThanInteger z 100))
               (lessThanInteger y 100)))
         (lessThanInteger x 100))
      50
      60
      70))
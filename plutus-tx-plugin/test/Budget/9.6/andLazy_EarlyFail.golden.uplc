(program
   1.1.0
   ((\x y z ->
       case
         (lessThanInteger x 100)
         [ False
         , (case (lessThanInteger y 100) [False, (lessThanInteger z 100)]) ])
      150
      60
      70))
(program
   1.1.0
   ((\x y z ->
       case
         (lessThanInteger x 100)
         [ False
         , (case
              (lessThanInteger y 100)
              [False, (case (lessThanInteger z 100) [False, True])]) ])
      50
      60
      150))
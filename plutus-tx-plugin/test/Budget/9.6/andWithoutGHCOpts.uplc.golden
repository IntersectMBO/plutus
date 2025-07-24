(program
   1.1.0
   ((\x y ->
       force
         (case
            (lessThanInteger x 3)
            [(delay False), (delay (lessThanInteger y 3))]))
      4
      4))
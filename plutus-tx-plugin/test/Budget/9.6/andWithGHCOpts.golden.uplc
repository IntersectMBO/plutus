(program
   1.2.0
   ((\x y -> case (lessThanInteger x 3) [False, (lessThanInteger y 3)]) 4 4))
(program
   1.2.0
   (\x y z ->
      multiplyInteger
        (multiplyInteger (addInteger x x) (addInteger y y))
        (addInteger z z)))
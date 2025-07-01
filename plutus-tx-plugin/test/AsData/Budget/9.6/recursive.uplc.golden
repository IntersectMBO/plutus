(program
   1.1.0
   ((\factorial x y z ->
       multiplyInteger
         (multiplyInteger (factorial x) (factorial y))
         (factorial z))
      ((\s -> s s)
         (\s x ->
            case
              (equalsInteger 0 x)
              [(multiplyInteger x ((\x -> s s x) (subtractInteger x 1))), 1]))))
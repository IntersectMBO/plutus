(program
   1.1.0
   ((\x y z ->
       case
         (lessThanInteger x 100)
         [ (\ds -> False)
         , (\ds ->
              case
                (lessThanInteger y 100)
                [(\ds -> False), (\ds -> lessThanInteger z 100)]
                ()) ]
         ())
      150
      60
      70))
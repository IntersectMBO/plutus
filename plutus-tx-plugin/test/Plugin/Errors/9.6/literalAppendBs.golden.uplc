program
  1.1.0
  (\x ->
     (\x ->
        case
          (constr 0
             [ (delay
                  ((\appendByteString -> appendByteString) appendByteString))
             , #68656c6c6f
             , x ])
          [(\appendByteString -> force appendByteString)])
       x)
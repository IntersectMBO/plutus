program
  1.1.0
  (\x ->
     (\x ->
        (\appendByteString -> force appendByteString)
          (delay ((\appendByteString -> appendByteString) appendByteString))
          #68656c6c6f
          x)
       x)
(program
   1.1.0
   (\ds ->
      case
        ds
        [ 0
        , (\ds xs ->
             addInteger
               1
               (case
                  xs
                  [ 0
                  , (\ds xs ->
                       addInteger
                         1
                         (case
                            xs
                            [ 0
                            , (\ds xs ->
                                 addInteger
                                   1
                                   ((\s -> s s)
                                      (\s ds ->
                                         case
                                           ds
                                           [ 0
                                           , (\ds xs ->
                                                addInteger 1 (s s xs)) ])
                                      xs)) ])) ])) ]))
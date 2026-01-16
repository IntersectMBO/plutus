(program
   1.1.0
   (\ds ->
      case
        ds
        [ 0
        , (\ds xs ->
             (\cse ->
                cse
                  (case
                     xs
                     [ 0
                     , (\ds xs ->
                          cse
                            (case
                               xs
                               [ 0
                               , (\ds xs ->
                                    cse
                                      ((\cse -> cse cse)
                                         (\s ds ->
                                            case
                                              ds
                                              [0, (\ds xs -> cse (s s xs))])
                                         xs)) ])) ]))
               (addInteger 1)) ]))
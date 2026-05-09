(program
   1.1.0
   ((\factorial ->
       (\fibonacci ->
          (\total n ->
             (\tot ->
                (\fac ->
                   (\fib ->
                      case
                        (lessThanInteger n 0)
                        [ (constr 0 [fib, fac, tot])
                        , ((\x -> error)
                             (force trace
                                "triple: negative input"
                                (constr 0 []))) ])
                     (fibonacci n))
                  (factorial n))
               (total n))
            ((\s -> s s)
               (\s n ->
                  case
                    (lessThanInteger n 0)
                    [ (case
                         (equalsInteger 0 n)
                         [ (addInteger n ((\x -> s s x) (subtractInteger n 1)))
                         , 0 ])
                    , ((\x -> error)
                         (force trace
                            "total: negative input"
                            (constr 0 []))) ])))
         ((\s -> s s)
            (\s ->
               (\fibonacci n ->
                  case
                    (lessThanInteger n 0)
                    [ (case
                         (equalsInteger 0 n)
                         [ (case
                              (equalsInteger 1 n)
                              [ (addInteger
                                   (fibonacci (subtractInteger n 1))
                                   (fibonacci (subtractInteger n 2)))
                              , 1 ])
                         , 0 ])
                    , ((\x -> error)
                         (force trace
                            "fibonacci: negative input"
                            (constr 0 []))) ])
                 (\x -> s s x))))
      ((\s -> s s)
         (\s n ->
            case
              (lessThanInteger n 0)
              [ (case
                   (equalsInteger 0 n)
                   [ (multiplyInteger n ((\x -> s s x) (subtractInteger n 1)))
                   , 1 ])
              , ((\x -> error)
                   (force trace
                      "factorial: negative input"
                      (constr 0 []))) ]))))
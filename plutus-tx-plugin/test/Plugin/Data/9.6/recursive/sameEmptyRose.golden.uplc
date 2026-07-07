program
  1.1.0
  ((\fix1 ->
      case
        (constr 0
           [ (delay (constr 0 []))
           , (delay (\arg_0 arg_1 -> constr 1 [arg_0, arg_1]))
           , (delay
                (\x ->
                   delay
                     (\case_Nil case_Cons -> case x [case_Nil, case_Cons]))) ])
        [ (force
             (delay
                (\Nil
                  Cons
                  List_match ->
                   force
                     (delay
                        (\EmptyRose
                          EmptyRose_match ->
                           (\g ->
                              (\f ->
                                 (\tup ->
                                    (\map ->
                                       (\map ->
                                          (\tup ->
                                             (\go ->
                                                (\go -> force go)
                                                  (go (delay (\x -> x))))
                                               (force tup (\arg_0 -> arg_0)))
                                            (delay
                                               (\f ->
                                                  f
                                                    (force
                                                       (force fix1)
                                                       (\go
                                                         arg ->
                                                          delay
                                                            (\x ->
                                                               (\x ->
                                                                  force
                                                                    g
                                                                    ((\x ->
                                                                        (\x ->
                                                                           force
                                                                             map
                                                                             (force
                                                                                (go
                                                                                   (delay
                                                                                      (\x ->
                                                                                         x))))
                                                                             (force
                                                                                f
                                                                                x))
                                                                          x)
                                                                       x))
                                                                 x))))))
                                         (map (delay (\x -> x))))
                                      (force tup (\arg_0 -> arg_0)))
                                   (delay
                                      (\f ->
                                         f
                                           (force
                                              (force fix1)
                                              (\map
                                                arg ->
                                                 delay
                                                   (\ds ->
                                                      (\ds
                                                        ds ->
                                                         force
                                                           (force
                                                              (force List_match
                                                                 ds)
                                                              (delay
                                                                 (force Nil))
                                                              (\x
                                                                xs ->
                                                                 delay
                                                                   (force
                                                                      Cons
                                                                      (ds x)
                                                                      (force
                                                                         (map
                                                                            (delay
                                                                               (\x ->
                                                                                  x)))
                                                                         ds
                                                                         xs)))))
                                                        ds))))))
                                (delay
                                   (\ds ->
                                      force (EmptyRose_match ds) (\x -> x))))
                             (delay
                                (\ds ->
                                   (\`$WEmptyRose` -> force `$WEmptyRose`)
                                     (delay
                                        (\conrep ->
                                           (\conrep -> EmptyRose conrep)
                                             conrep))
                                     ds))))
                     (\arg_0 -> constr 0 [arg_0])
                     (\x ->
                        delay
                          (\case_EmptyRose -> case x [case_EmptyRose]))))) ])
     (delay
        (delay
           (\f ->
              force (delay (\s -> s s))
                (\s -> f (\x -> force (delay (\s -> s s)) s x))))))
program
  1.1.0
  ((\fixBy ->
      (\fix3 ->
         (\fix1 ->
            force
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
                                                 (\g ->
                                                    (\f ->
                                                       (\go ->
                                                          (\g ->
                                                             (\f -> force go)
                                                               (f
                                                                  (delay
                                                                     (\x ->
                                                                        x))))
                                                            (g
                                                               (delay
                                                                  (\x -> x))))
                                                         (go (delay (\x -> x))))
                                                      (force tup
                                                         (\arg_0 arg_1 arg_2 ->
                                                            arg_2)))
                                                   (force tup
                                                      (\arg_0 arg_1 arg_2 ->
                                                         arg_1)))
                                                (force tup
                                                   (\arg_0 arg_1 arg_2 ->
                                                      arg_0)))
                                             (force
                                                (force
                                                   (force
                                                      (force
                                                         (force (force fix3)))))
                                                (delay
                                                   (\choose
                                                     go
                                                     g
                                                     f ->
                                                      choose
                                                        (\arg ->
                                                           delay
                                                             (\x ->
                                                                (\x ->
                                                                   force
                                                                     g
                                                                     (force
                                                                        (f
                                                                           (delay
                                                                              (\x ->
                                                                                 x)))
                                                                        x))
                                                                  x))
                                                        (\arg ->
                                                           delay
                                                             (force
                                                                map
                                                                (force
                                                                   (go
                                                                      (delay
                                                                         (\x ->
                                                                            x))))))
                                                        (\arg ->
                                                           delay
                                                             (\x ->
                                                                (\x ->
                                                                   force
                                                                     (g
                                                                        (delay
                                                                           (\x ->
                                                                              x)))
                                                                     (force f
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
                         delay (\case_EmptyRose -> case x [case_EmptyRose]))))
              (delay (constr 0 []))
              (delay (\arg_0 arg_1 -> constr 1 [arg_0, arg_1]))
              (delay
                 (\x ->
                    delay
                      (\case_Nil case_Cons -> case x [case_Nil, case_Cons]))))
           (delay
              (delay
                 (\f ->
                    force (delay (\s -> s s))
                      (\s -> f (\x -> force (delay (\s -> s s)) s x))))))
        (delay
           (delay
              (delay
                 (delay
                    (delay
                       (delay
                          (\f ->
                             force fixBy
                               (\k ->
                                  delay
                                    (\h ->
                                       h
                                         (\x -> force k (\f_0 f_1 f_2 -> f_0 x))
                                         (\x -> force k (\f_0 f_1 f_2 -> f_1 x))
                                         (\x ->
                                            force k (\f_0 f_1 f_2 -> f_2 x))))
                               f))))))))
     (delay
        (\by ->
           force
             (force
                (delay
                   (delay
                      (\f ->
                         force (delay (\s -> s s))
                           (\s -> f (\x -> force (delay (\s -> s s)) s x))))))
             (\rec h ->
                delay
                  (\fr ->
                     force (by (delay (\fq -> force (rec h) (force h fq))))
                       fr)))))
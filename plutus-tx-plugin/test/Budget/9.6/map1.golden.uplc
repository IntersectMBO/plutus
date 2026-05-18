(program
   1.1.0
   ((\forced ->
       (\`$dmenumFromTo_$cenumFromTo` n ->
          (\nt ->
             (\nt ->
                (\lookup ->
                   constr 0
                     [ (case
                          (constr 0 [(\i -> iData i), unIData, n, nt])
                          [lookup])
                     , (case
                          (constr 0
                             [(\i -> iData i), unIData, (addInteger 5 n), nt])
                          [lookup])
                     , (case
                          (constr 0
                             [(\i -> iData i), unIData, (addInteger 10 n), nt])
                          [lookup])
                     , (case
                          (constr 0
                             [(\i -> iData i), unIData, (addInteger 20 n), nt])
                          [lookup])
                     , (case
                          (constr 0
                             [(\i -> iData i), unIData, (addInteger 5 n), nt])
                          [lookup]) ])
                  (\`$dToData` `$dUnsafeFromData` ds ds ->
                     (\k ->
                        (\s ->
                           case
                             (s s ds)
                             [ (\a -> constr 0 [(`$dUnsafeFromData` a)])
                             , (constr 1 []) ])
                          (\s xs ->
                             case
                               xs
                               [ (\hd ->
                                    case
                                      (equalsData k (case hd [(\l r -> l)]))
                                      [ (\x -> s s x)
                                      , (\ds ->
                                           constr 0
                                             [(case hd [(\l r -> r)])]) ])
                               , (constr 1 []) ]))
                       (`$dToData` ds)))
               ((\k ->
                   (\s -> s s nt)
                     (\s xs ->
                        case
                          xs
                          [ (\hd ->
                               case
                                 (equalsData k (case hd [(\l r -> l)]))
                                 [(\eta -> forced hd (s s eta)), (\x -> x)])
                          , [] ]))
                  (iData (addInteger 5 n))))
            ((\z ->
                (\s -> s s (`$dmenumFromTo_$cenumFromTo` 1 10))
                  (\s ds ->
                     case
                       ds
                       [ z
                       , (\y ys ->
                            (\ds ->
                               (\k ->
                                  (\a ->
                                     (\nilCase ->
                                        (\s -> s s ds)
                                          (\s xs ->
                                             case
                                               xs
                                               [ (\hd ->
                                                    case
                                                      (equalsData
                                                         k
                                                         (case
                                                            hd
                                                            [(\l r -> l)]))
                                                      [ (\eta ->
                                                           forced hd (s s eta))
                                                      , (forced
                                                           (mkPairData k a)) ])
                                               , nilCase ]))
                                       (forced (mkPairData k a) []))
                                    (iData y))
                                 (iData (addInteger n y)))
                              (s s ys)) ]))
               (forced (mkPairData (iData n) (I 0)) [])))
         ((\s -> s s)
            (\s x lim ->
               case
                 (lessThanInteger lim x)
                 [ (constr 1
                      [ x
                      , ((\x -> case (constr 0 [s, x, lim]) [s])
                           (addInteger 1 x)) ])
                 , (constr 0 []) ])))
      (force mkCons)))
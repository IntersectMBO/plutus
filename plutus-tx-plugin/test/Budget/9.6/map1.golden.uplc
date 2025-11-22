(program
   1.1.0
   ((\`$fEnumBool_$cenumFromTo` n ->
       (\nt ->
          (\nt ->
             (\lookup ->
                constr 0
                  [ (case (constr 0 [(\i -> iData i), unIData, n, nt]) [lookup])
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
                  case
                    ((\k ->
                        (\s -> s s)
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
                               , (constr 1 []) ])
                          ds)
                       (`$dToData` ds))
                    [(\a -> constr 0 [(`$dUnsafeFromData` a)]), (constr 1 [])]))
            ((\k ->
                (\s -> s s)
                  (\s xs ->
                     case
                       xs
                       [ (\hd ->
                            case
                              (equalsData k (case hd [(\l r -> l)]))
                              [(\eta -> force mkCons hd (s s eta)), (\x -> x)])
                       , [] ]))
               (iData (addInteger 5 n))
               nt))
         ((\z ->
             (\go eta -> go eta)
               ((\s -> s s)
                  (\s ds ->
                     case
                       ds
                       [ z
                       , (\y ys ->
                            (\ds ->
                               (\k ->
                                  (\a ->
                                     (\nilCase ->
                                        (\s -> s s)
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
                                                           force mkCons
                                                             hd
                                                             (s s eta))
                                                      , (force mkCons
                                                           (mkPairData k a)) ])
                                               , nilCase ])
                                          ds)
                                       (force mkCons (mkPairData k a) []))
                                    (iData y))
                                 (iData (addInteger n y)))
                              (s s ys)) ])))
            (force mkCons (mkPairData (iData n) (I 0)) [])
            (`$fEnumBool_$cenumFromTo` 1 10)))
      ((\s -> s s)
         (\s x lim ->
            case
              (lessThanEqualsInteger x lim)
              [ (constr 0 [])
              , (constr 1 [x, ((\x -> s s x) (addInteger 1 x) lim)]) ]))))
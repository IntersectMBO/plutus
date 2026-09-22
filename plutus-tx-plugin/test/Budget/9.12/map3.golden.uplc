(program
   1.1.0
   ((\forced
      forced ->
       (\`$fToDataThese_$ctoBuiltinData` ->
          (\`$dToData` ->
             (\`$dToData` ->
                (\goList
                  n ->
                   (\unsafeFromSOPList ->
                      (\nt ->
                         (\nt ->
                            (\nt ->
                               (\s ->
                                  s
                                    s
                                    ((\s ->
                                        s s nt)
                                       (\s
                                         xs ->
                                          case
                                            xs
                                            [ (\hd
                                                tl ->
                                                 constr 1
                                                   [ (constr 0
                                                        [ (unIData
                                                             (case
                                                                hd
                                                                [(\l r -> l)]))
                                                        , (case
                                                             (case
                                                                hd
                                                                [(\l r -> r)])
                                                             [ (\ds ->
                                                                  constr 2
                                                                    [ (unIData
                                                                         (forced
                                                                            ds)) ])
                                                             , (\ds ->
                                                                  constr 0
                                                                    [ (unIData
                                                                         (forced
                                                                            ds)) ])
                                                             , (\ds ->
                                                                  case
                                                                    ds
                                                                    [ (\ds
                                                                        ds ->
                                                                         constr 1
                                                                           [ (unIData
                                                                                ds)
                                                                           , (unIData
                                                                                (forced
                                                                                   ds)) ]) ]) ]) ])
                                                   , (s s tl) ])
                                            , (constr 0 []) ])))
                                 (\s ds ->
                                    case
                                      ds
                                      [ (constr 0 [])
                                      , (\x xs ->
                                           constr 1
                                             [ (case
                                                  x
                                                  [ (\c a ->
                                                       constr 0
                                                         [ c
                                                         , (case
                                                              a
                                                              [ (\b -> b)
                                                              , (\a b ->
                                                                   addInteger
                                                                     a
                                                                     b)
                                                              , (\a ->
                                                                   a) ]) ]) ])
                                             , (s s xs) ]) ]))
                              ((\right ->
                                  (\s ->
                                     s s nt)
                                    (\s
                                      xs ->
                                       case
                                         xs
                                         [ (\hd
                                             tl ->
                                              (\v ->
                                                 (\k ->
                                                    (\s ->
                                                       case
                                                         (s s nt)
                                                         [ (\r ->
                                                              forced
                                                                (mkPairData
                                                                   k
                                                                   (case
                                                                      (constr 0
                                                                         [ `$dToData`
                                                                         , `$dToData`
                                                                         , (constr 1
                                                                              [ (unIData
                                                                                   v)
                                                                              , (unIData
                                                                                   r) ]) ])
                                                                      [ `$fToDataThese_$ctoBuiltinData` ]))
                                                                (s s tl))
                                                         , (forced
                                                              (mkPairData
                                                                 k
                                                                 (case
                                                                    (constr 0
                                                                       [ `$dToData`
                                                                       , `$dToData`
                                                                       , (constr 2
                                                                            [ (unIData
                                                                                 v) ]) ])
                                                                    [ `$fToDataThese_$ctoBuiltinData` ]))
                                                              (s s tl)) ])
                                                      (\s
                                                        xs ->
                                                         case
                                                           xs
                                                           [ (\hd ->
                                                                case
                                                                  (equalsData
                                                                     k
                                                                     (case
                                                                        hd
                                                                        [ (\l
                                                                            r ->
                                                                             l) ]))
                                                                  [ (\x ->
                                                                       s s x)
                                                                  , (\ds ->
                                                                       constr 0
                                                                         [ (case
                                                                              hd
                                                                              [ (\l
                                                                                  r ->
                                                                                   r) ]) ]) ])
                                                           , (constr 1 []) ]))
                                                   (case hd [(\l r -> l)]))
                                                (case hd [(\l r -> r)]))
                                         , right ]))
                                 ((\s ->
                                     s s nt)
                                    (\s
                                      xs ->
                                       case
                                         xs
                                         [ (\hd
                                             tl ->
                                              (\tl' ->
                                                 (\k ->
                                                    (\s ->
                                                       case
                                                         (s s nt)
                                                         [ (forced
                                                              (mkPairData
                                                                 k
                                                                 (case
                                                                    (constr 0
                                                                       [ `$dToData`
                                                                       , `$dToData`
                                                                       , (constr 0
                                                                            [ (unIData
                                                                                 (case
                                                                                    hd
                                                                                    [ (\l
                                                                                        r ->
                                                                                         r) ])) ]) ])
                                                                    [ `$fToDataThese_$ctoBuiltinData` ]))
                                                              tl')
                                                         , tl' ])
                                                      (\s
                                                        xs ->
                                                         case
                                                           xs
                                                           [ (\hd ->
                                                                case
                                                                  (equalsData
                                                                     k
                                                                     (case
                                                                        hd
                                                                        [ (\l
                                                                            r ->
                                                                             l) ]))
                                                                  [ (\x ->
                                                                       s s x)
                                                                  , (\ds ->
                                                                       True) ])
                                                           , False ]))
                                                   (case hd [(\l r -> l)]))
                                                (s s tl))
                                         , [] ]))))
                           (case
                              (constr 0
                                 [ (\i -> iData i)
                                 , (\i -> iData i)
                                 , (constr 1
                                      [ (constr 0 [(addInteger 1 n), 1])
                                      , (constr 1
                                           [ (constr 0 [(addInteger 2 n), 2])
                                           , (constr 1
                                                [ (constr 0
                                                     [(addInteger 3 n), 3])
                                                , (constr 1
                                                     [ (constr 0
                                                          [(addInteger 4 n), 4])
                                                     , (constr 1
                                                          [ (constr 0
                                                               [ (addInteger
                                                                    5
                                                                    n)
                                                               , 5 ])
                                                          , (constr 0
                                                               [  ]) ]) ]) ]) ]) ]) ])
                              [unsafeFromSOPList]))
                        (case
                           (constr 0
                              [ (\i -> iData i)
                              , (\i -> iData i)
                              , (constr 1
                                   [ (constr 0 [(addInteger 3 n), 30])
                                   , (constr 1
                                        [ (constr 0 [(addInteger 4 n), 40])
                                        , (constr 1
                                             [ (constr 0 [(addInteger 6 n), 60])
                                             , (constr 1
                                                  [ (constr 0
                                                       [(addInteger 7 n), 70])
                                                  , (constr 0 []) ]) ]) ]) ]) ])
                           [unsafeFromSOPList]))
                     (\`$dToData` `$dToData` ->
                        (\go eta -> goList (go eta))
                          ((\s -> s s)
                             (\s ds ->
                                case
                                  ds
                                  [ (constr 0 [])
                                  , (\x xs ->
                                       constr 1
                                         [ (case
                                              x
                                              [ (\k a ->
                                                   constr 0
                                                     [ (`$dToData` k)
                                                     , (`$dToData` a) ]) ])
                                         , (s s xs) ]) ]))))
                  ((\s -> s s)
                     (\s ds ->
                        case
                          ds
                          [ []
                          , (\d ds ->
                               forced
                                 (case d [(\d d -> mkPairData d d)])
                                 (s s ds)) ])))
               (\i -> iData i))
            (\i -> iData i))
         (\`$dToData` `$dToData` ds ->
            case
              ds
              [ (\arg -> constrData 1 (forced (`$dToData` arg) []))
              , (\arg arg ->
                   constrData
                     2
                     (forced (`$dToData` arg) (forced (`$dToData` arg) [])))
              , (\arg -> constrData 0 (forced (`$dToData` arg) [])) ]))
      (force mkCons)
      (force headList)))
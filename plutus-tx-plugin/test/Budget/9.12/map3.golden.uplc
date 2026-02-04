(program
   1.1.0
   ((\safeAppend ->
       (\lookup' ->
          (\`$fToDataThese_$ctoBuiltinData` ->
             (\`$dToData` ->
                (\`$dToData` ->
                   (\goList
                     n ->
                      (\unsafeFromSOPList ->
                         (\nt ->
                            (\goLeft ->
                               (\nt ->
                                  (\goRight ->
                                     (\nt ->
                                        (\s ->
                                           s s)
                                          (\s
                                            ds ->
                                             case
                                               ds
                                               [ (constr 0 [])
                                               , (\x
                                                   xs ->
                                                    constr 1
                                                      [ (case
                                                           x
                                                           [ (\c
                                                               a ->
                                                                constr 0
                                                                  [ c
                                                                  , (case
                                                                       a
                                                                       [ (\b ->
                                                                            b)
                                                                       , (\a
                                                                           b ->
                                                                            addInteger
                                                                              a
                                                                              b)
                                                                       , (\a ->
                                                                            a) ]) ]) ])
                                                      , (s s xs) ]) ])
                                          ((\s ->
                                              s s)
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
                                                                      [ (\l
                                                                          r ->
                                                                           l) ]))
                                                              , (case
                                                                   (unConstrData
                                                                      (case
                                                                         hd
                                                                         [ (\l
                                                                             r ->
                                                                              r) ]))
                                                                   [ (\index
                                                                       args ->
                                                                        case
                                                                          index
                                                                          [ (\ds ->
                                                                               constr 2
                                                                                 [ (unIData
                                                                                      (force
                                                                                         headList
                                                                                         ds)) ])
                                                                          , (\ds ->
                                                                               constr 0
                                                                                 [ (unIData
                                                                                      (force
                                                                                         headList
                                                                                         ds)) ])
                                                                          , (\ds ->
                                                                               constr 1
                                                                                 [ (unIData
                                                                                      (force
                                                                                         headList
                                                                                         ds))
                                                                                 , (unIData
                                                                                      (force
                                                                                         headList
                                                                                         (force
                                                                                            tailList
                                                                                            ds))) ]) ]
                                                                          args) ]) ])
                                                         , (s s tl) ])
                                                  , (constr 0 []) ])
                                             nt))
                                       (safeAppend (goLeft nt) (goRight nt)))
                                    ((\s ->
                                        s s)
                                       (\s
                                         xs ->
                                          case
                                            xs
                                            [ (\hd
                                                tl ->
                                                 (\v ->
                                                    (\k ->
                                                       case
                                                         (lookup' k nt)
                                                         [ (\r ->
                                                              force
                                                                mkCons
                                                                (mkPairData
                                                                   k
                                                                   (`$fToDataThese_$ctoBuiltinData`
                                                                      `$dToData`
                                                                      `$dToData`
                                                                      (constr 1
                                                                         [ (unIData
                                                                              v)
                                                                         , (unIData
                                                                              r) ])))
                                                                (s s tl))
                                                         , (force
                                                              mkCons
                                                              (mkPairData
                                                                 k
                                                                 (`$fToDataThese_$ctoBuiltinData`
                                                                    `$dToData`
                                                                    `$dToData`
                                                                    (constr 0
                                                                       [ (unIData
                                                                            v) ])))
                                                              (s s tl)) ])
                                                      (case hd [(\l r -> l)]))
                                                   (case hd [(\l r -> r)]))
                                            , [] ])))
                                 (unsafeFromSOPList
                                    (\i -> iData i)
                                    (\i -> iData i)
                                    (constr 1
                                       [ (constr 0 [(addInteger 1 n), 1])
                                       , (constr 1
                                            [ (constr 0 [(addInteger 2 n), 2])
                                            , (constr 1
                                                 [ (constr 0
                                                      [(addInteger 3 n), 3])
                                                 , (constr 1
                                                      [ (constr 0
                                                           [ (addInteger 4 n)
                                                           , 4 ])
                                                      , (constr 1
                                                           [ (constr 0
                                                                [ (addInteger
                                                                     5
                                                                     n)
                                                                , 5 ])
                                                           , (constr 0
                                                                [  ]) ]) ]) ]) ]) ])))
                              ((\s ->
                                  s s)
                                 (\s
                                   xs ->
                                    case
                                      xs
                                      [ (\hd
                                          tl ->
                                           (\v ->
                                              (\k ->
                                                 case
                                                   (lookup' k nt)
                                                   [ (\r ->
                                                        force
                                                          mkCons
                                                          (mkPairData
                                                             k
                                                             (`$fToDataThese_$ctoBuiltinData`
                                                                `$dToData`
                                                                `$dToData`
                                                                (constr 1
                                                                   [ (unIData v)
                                                                   , (unIData
                                                                        r) ])))
                                                          (s s tl))
                                                   , (force
                                                        mkCons
                                                        (mkPairData
                                                           k
                                                           (`$fToDataThese_$ctoBuiltinData`
                                                              `$dToData`
                                                              `$dToData`
                                                              (constr 2
                                                                 [ (unIData
                                                                      v) ])))
                                                        (s s tl)) ])
                                                (case hd [(\l r -> l)]))
                                             (case hd [(\l r -> r)]))
                                      , [] ])))
                           (unsafeFromSOPList
                              (\i -> iData i)
                              (\i -> iData i)
                              (constr 1
                                 [ (constr 0 [(addInteger 3 n), 30])
                                 , (constr 1
                                      [ (constr 0 [(addInteger 4 n), 40])
                                      , (constr 1
                                           [ (constr 0 [(addInteger 6 n), 60])
                                           , (constr 1
                                                [ (constr 0
                                                     [(addInteger 7 n), 70])
                                                , (constr 0 []) ]) ]) ]) ])))
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
                                  force mkCons
                                    (case d [(\d d -> mkPairData d d)])
                                    (s s ds)) ])))
                  (\i -> iData i))
               (\i -> iData i))
            (\`$dToData` `$dToData` ds ->
               case
                 ds
                 [ (\arg -> constrData 1 (force mkCons (`$dToData` arg) []))
                 , (\arg arg ->
                      constrData
                        2
                        (force mkCons
                           (`$dToData` arg)
                           (force mkCons (`$dToData` arg) [])))
                 , (\arg -> constrData 0 (force mkCons (`$dToData` arg) [])) ]))
         (\k ->
            (\go m -> go m)
              ((\s -> s s)
                 (\s xs ->
                    case
                      xs
                      [ (\hd ->
                           case
                             (equalsData k (case hd [(\l r -> l)]))
                             [ (\x -> s s x)
                             , (\ds -> constr 0 [(case hd [(\l r -> r)])]) ])
                      , (constr 1 []) ]))))
      ((\s -> s s)
         (\s xs xs ->
            case
              xs
              [ (\hd tl ->
                   (\v ->
                      (\k ->
                         (\eta ->
                            (\nilCase ->
                               (\s -> s s)
                                 (\s xs ->
                                    case
                                      xs
                                      [ (\hd ->
                                           case
                                             (equalsData
                                                k
                                                (case hd [(\l r -> l)]))
                                             [ (\eta ->
                                                  force mkCons hd (s s eta))
                                             , (force mkCons
                                                  (mkPairData k v)) ])
                                      , nilCase ])
                                 eta)
                              (force mkCons (mkPairData k v) []))
                           (s s tl xs))
                        (case hd [(\l r -> l)]))
                     (case hd [(\l r -> r)]))
              , xs ]))))
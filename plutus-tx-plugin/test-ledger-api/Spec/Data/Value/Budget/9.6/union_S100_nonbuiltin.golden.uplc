(program
   1.1.0
   ((\map ->
       (\`$fToDataMap_$ctoBuiltinData` ->
          (\`$fUnsafeFromDataThese_$cunsafeFromBuiltinData` ->
             (\`$fToDataThese_$ctoBuiltinData` ->
                (\`$fToDataInteger_$ctoBuiltinData` ->
                   (\safeAppend
                     bd
                     bd ->
                      (\lookup' ->
                         (\value ->
                            case
                              (lookup' (B #) value)
                              [ (\a ->
                                   case
                                     (lookup' (B #) (unMapData a))
                                     [(\a -> unIData a), 0])
                              , 0 ])
                           ((\ls ->
                               (\rs ->
                                  case
                                    (constr 0
                                       [ (\eta -> unMapData eta)
                                       , `$fToDataMap_$ctoBuiltinData`
                                       , (case
                                            (constr 0
                                               [ (`$fUnsafeFromDataThese_$cunsafeFromBuiltinData`
                                                    unIData
                                                    unIData)
                                               , `$fToDataInteger_$ctoBuiltinData`
                                               , (\k' ->
                                                    case
                                                      k'
                                                      [ (\b -> addInteger 0 b)
                                                      , (\a b -> addInteger a b)
                                                      , (\a ->
                                                           addInteger 0 a) ]) ])
                                            [map])
                                       , ((\union ->
                                             case
                                               (constr 0
                                                  [ (`$fUnsafeFromDataThese_$cunsafeFromBuiltinData`
                                                       (\eta -> unMapData eta)
                                                       (\eta -> unMapData eta))
                                                  , `$fToDataMap_$ctoBuiltinData`
                                                  , (\k ->
                                                       case
                                                         k
                                                         [ (\b ->
                                                              case
                                                                (constr 0
                                                                   [ unIData
                                                                   , (`$fToDataThese_$ctoBuiltinData`
                                                                        `$fToDataInteger_$ctoBuiltinData`
                                                                        `$fToDataInteger_$ctoBuiltinData`)
                                                                   , (\ds ->
                                                                        constr 0
                                                                          [ds])
                                                                   , b ])
                                                                [map])
                                                         , (\a
                                                             b ->
                                                              case
                                                                (constr 0
                                                                   [ unIData
                                                                   , unIData
                                                                   , `$fToDataInteger_$ctoBuiltinData`
                                                                   , `$fToDataInteger_$ctoBuiltinData`
                                                                   , a
                                                                   , b ])
                                                                [union])
                                                         , (\a ->
                                                              case
                                                                (constr 0
                                                                   [ unIData
                                                                   , (`$fToDataThese_$ctoBuiltinData`
                                                                        `$fToDataInteger_$ctoBuiltinData`
                                                                        `$fToDataInteger_$ctoBuiltinData`)
                                                                   , (\ds ->
                                                                        constr 2
                                                                          [ds])
                                                                   , a ])
                                                                [map]) ])
                                                  , (case
                                                       (constr 0
                                                          [ (\eta ->
                                                               unMapData eta)
                                                          , (\eta ->
                                                               unMapData eta)
                                                          , `$fToDataMap_$ctoBuiltinData`
                                                          , `$fToDataMap_$ctoBuiltinData`
                                                          , ls
                                                          , rs ])
                                                       [union]) ])
                                               [map])
                                            (\`$dUnsafeFromData`
                                              `$dUnsafeFromData`
                                              `$dToData`
                                              `$dToData`
                                              ds ->
                                               (\goRight
                                                 ds ->
                                                  safeAppend
                                                    ((\s ->
                                                        s s ds)
                                                       (\s
                                                         xs ->
                                                          case
                                                            xs
                                                            [ (\hd
                                                                tl ->
                                                                 (\v ->
                                                                    (\k ->
                                                                       case
                                                                         (lookup'
                                                                            k
                                                                            ds)
                                                                         [ (\r ->
                                                                              force
                                                                                mkCons
                                                                                (mkPairData
                                                                                   k
                                                                                   (case
                                                                                      (constr 0
                                                                                         [ `$dToData`
                                                                                         , `$dToData`
                                                                                         , (constr 1
                                                                                              [ (`$dUnsafeFromData`
                                                                                                   v)
                                                                                              , (`$dUnsafeFromData`
                                                                                                   r) ]) ])
                                                                                      [ `$fToDataThese_$ctoBuiltinData` ]))
                                                                                (s
                                                                                   s
                                                                                   tl))
                                                                         , (force
                                                                              mkCons
                                                                              (mkPairData
                                                                                 k
                                                                                 (case
                                                                                    (constr 0
                                                                                       [ `$dToData`
                                                                                       , `$dToData`
                                                                                       , (constr 2
                                                                                            [ (`$dUnsafeFromData`
                                                                                                 v) ]) ])
                                                                                    [ `$fToDataThese_$ctoBuiltinData` ]))
                                                                              (s
                                                                                 s
                                                                                 tl)) ])
                                                                      (case
                                                                         hd
                                                                         [ (\l
                                                                             r ->
                                                                              l) ]))
                                                                   (case
                                                                      hd
                                                                      [ (\l
                                                                          r ->
                                                                           r) ]))
                                                            , [] ]))
                                                    (goRight ds))
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
                                                                      (lookup'
                                                                         k
                                                                         ds)
                                                                      [ (\r ->
                                                                           force
                                                                             mkCons
                                                                             (mkPairData
                                                                                k
                                                                                (case
                                                                                   (constr 0
                                                                                      [ `$dToData`
                                                                                      , `$dToData`
                                                                                      , (constr 1
                                                                                           [ (`$dUnsafeFromData`
                                                                                                v)
                                                                                           , (`$dUnsafeFromData`
                                                                                                r) ]) ])
                                                                                   [ `$fToDataThese_$ctoBuiltinData` ]))
                                                                             (s
                                                                                s
                                                                                tl))
                                                                      , (force
                                                                           mkCons
                                                                           (mkPairData
                                                                              k
                                                                              (case
                                                                                 (constr 0
                                                                                    [ `$dToData`
                                                                                    , `$dToData`
                                                                                    , (constr 0
                                                                                         [ (`$dUnsafeFromData`
                                                                                              v) ]) ])
                                                                                 [ `$fToDataThese_$ctoBuiltinData` ]))
                                                                           (s
                                                                              s
                                                                              tl)) ])
                                                                   (case
                                                                      hd
                                                                      [ (\l
                                                                          r ->
                                                                           l) ]))
                                                                (case
                                                                   hd
                                                                   [ (\l r ->
                                                                        r) ]))
                                                         , [] ])))) ])
                                    [map])
                                 (unMapData bd))
                              (unMapData bd)))
                        (\k ->
                           (\go m -> go m)
                             ((\s -> s s)
                                (\s xs ->
                                   case
                                     xs
                                     [ (\hd ->
                                          case
                                            (equalsData
                                               k
                                               (case hd [(\l r -> l)]))
                                            [ (\x -> s s x)
                                            , (\ds ->
                                                 constr 0
                                                   [(case hd [(\l r -> r)])]) ])
                                     , (constr 1 []) ]))))
                     ((\s -> s s)
                        (\s xs xs ->
                           case
                             xs
                             [ (\hd tl ->
                                  (\v ->
                                     (\k ->
                                        (\eta ->
                                           (\cse ->
                                              (\nilCase ->
                                                 (\s -> s s eta)
                                                   (\s xs ->
                                                      case
                                                        xs
                                                        [ (\hd ->
                                                             case
                                                               (equalsData
                                                                  k
                                                                  (case
                                                                     hd
                                                                     [ (\l r ->
                                                                          l) ]))
                                                               [ (\eta ->
                                                                    force mkCons
                                                                      hd
                                                                      (s s eta))
                                                               , cse ])
                                                        , nilCase ]))
                                                (cse []))
                                             (force mkCons (mkPairData k v)))
                                          (case (constr 0 [s, tl, xs]) [s]))
                                       (case hd [(\l r -> l)]))
                                    (case hd [(\l r -> r)]))
                             , xs ])))
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
                    , (\arg ->
                         constrData 0 (force mkCons (`$dToData` arg) [])) ]))
            (\`$dUnsafeFromData` `$dUnsafeFromData` d ->
               case
                 (unConstrData d)
                 [ (\index args ->
                      case
                        index
                        [ (\ds ->
                             constr 2
                               [(`$dUnsafeFromData` (force headList ds))])
                        , (\ds ->
                             constr 0
                               [(`$dUnsafeFromData` (force headList ds))])
                        , (\ds ->
                             constr 1
                               [ (`$dUnsafeFromData` (force headList ds))
                               , (`$dUnsafeFromData`
                                    (force headList (force tailList ds))) ]) ]
                        args) ]))
         (\ds -> mapData ds))
      (\`$dUnsafeFromData` `$dToData` f ->
         (\s -> s s)
           (\s xs ->
              case
                xs
                [ (\hd eta ->
                     force mkCons
                       (mkPairData
                          (case hd [(\l r -> l)])
                          (`$dToData`
                             (f (`$dUnsafeFromData` (case hd [(\l r -> r)])))))
                       (s s eta))
                , [] ]))))
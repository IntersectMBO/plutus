(program
   1.1.0
   ((\go ->
       (\`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData` ->
          (\`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData` ->
             (\`$fUnsafeFromDataDCert_$cunsafeFromBuiltinData` ->
                (\go ->
                   (\`$fUnsafeFromDataMap_$cunsafeFromBuiltinData` ->
                      (\`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData` ->
                         (\go ->
                            (\`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData` ->
                               (\`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData` ->
                                  (\`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` ->
                                     (\go ->
                                        (\go
                                          obsScriptCred
                                          ctx ->
                                           case
                                             (case
                                                (unConstrData ctx)
                                                [ (\index
                                                    args ->
                                                     case
                                                       index
                                                       [ (\ds ->
                                                            (\`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` ->
                                                               constr 0
                                                                 [ (case
                                                                      (unConstrData
                                                                         (force
                                                                            headList
                                                                            ds))
                                                                      [ (\index
                                                                          args ->
                                                                           case
                                                                             index
                                                                             [ (\ds ->
                                                                                  (\l ->
                                                                                     (\l ->
                                                                                        (\l ->
                                                                                           (\l ->
                                                                                              (\l ->
                                                                                                 (\l ->
                                                                                                    (\l ->
                                                                                                       (\l ->
                                                                                                          (\l ->
                                                                                                             (\l ->
                                                                                                                (\`$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData` ->
                                                                                                                   (\cse ->
                                                                                                                      (\cse ->
                                                                                                                         (\arg_0
                                                                                                                           arg_1
                                                                                                                           arg_2
                                                                                                                           arg_3
                                                                                                                           arg_4
                                                                                                                           arg_5
                                                                                                                           arg_6
                                                                                                                           arg_7
                                                                                                                           arg_8
                                                                                                                           arg_9
                                                                                                                           arg_10
                                                                                                                           arg_11 ->
                                                                                                                            constr 0
                                                                                                                              [ arg_0
                                                                                                                              , arg_1
                                                                                                                              , arg_2
                                                                                                                              , arg_3
                                                                                                                              , arg_4
                                                                                                                              , arg_5
                                                                                                                              , arg_6
                                                                                                                              , arg_7
                                                                                                                              , arg_8
                                                                                                                              , arg_9
                                                                                                                              , arg_10
                                                                                                                              , arg_11 ])
                                                                                                                           (go
                                                                                                                              (unListData
                                                                                                                                 (force
                                                                                                                                    headList
                                                                                                                                    ds)))
                                                                                                                           (go
                                                                                                                              (unListData
                                                                                                                                 (force
                                                                                                                                    headList
                                                                                                                                    l)))
                                                                                                                           (go
                                                                                                                              (unListData
                                                                                                                                 (force
                                                                                                                                    headList
                                                                                                                                    l)))
                                                                                                                           (cse
                                                                                                                              (force
                                                                                                                                 headList
                                                                                                                                 l))
                                                                                                                           (cse
                                                                                                                              (force
                                                                                                                                 headList
                                                                                                                                 l))
                                                                                                                           (go
                                                                                                                              (unListData
                                                                                                                                 (force
                                                                                                                                    headList
                                                                                                                                    l)))
                                                                                                                           (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                                                                              `$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                                                                                              unIData
                                                                                                                              (force
                                                                                                                                 headList
                                                                                                                                 l))
                                                                                                                           (case
                                                                                                                              (unConstrData
                                                                                                                                 (force
                                                                                                                                    headList
                                                                                                                                    l))
                                                                                                                              [ (\index
                                                                                                                                  args ->
                                                                                                                                   case
                                                                                                                                     index
                                                                                                                                     [ (\ds ->
                                                                                                                                          (\`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData` ->
                                                                                                                                             (\`$fUnsafeFromDataBool_$cunsafeFromBuiltinData` ->
                                                                                                                                                constr 0
                                                                                                                                                  [ (case
                                                                                                                                                       (unConstrData
                                                                                                                                                          (force
                                                                                                                                                             headList
                                                                                                                                                             ds))
                                                                                                                                                       [ (\index
                                                                                                                                                           args ->
                                                                                                                                                            case
                                                                                                                                                              index
                                                                                                                                                              [ (\ds ->
                                                                                                                                                                   constr 0
                                                                                                                                                                     [ (`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData`
                                                                                                                                                                          unIData
                                                                                                                                                                          (force
                                                                                                                                                                             headList
                                                                                                                                                                             ds))
                                                                                                                                                                     , (`$fUnsafeFromDataBool_$cunsafeFromBuiltinData`
                                                                                                                                                                          (force
                                                                                                                                                                             headList
                                                                                                                                                                             (force
                                                                                                                                                                                tailList
                                                                                                                                                                                ds))) ]) ]
                                                                                                                                                              args) ])
                                                                                                                                                  , (case
                                                                                                                                                       (unConstrData
                                                                                                                                                          (force
                                                                                                                                                             headList
                                                                                                                                                             (force
                                                                                                                                                                tailList
                                                                                                                                                                ds)))
                                                                                                                                                       [ (\index
                                                                                                                                                           args ->
                                                                                                                                                            case
                                                                                                                                                              index
                                                                                                                                                              [ (\ds ->
                                                                                                                                                                   constr 0
                                                                                                                                                                     [ (`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData`
                                                                                                                                                                          unIData
                                                                                                                                                                          (force
                                                                                                                                                                             headList
                                                                                                                                                                             ds))
                                                                                                                                                                     , (`$fUnsafeFromDataBool_$cunsafeFromBuiltinData`
                                                                                                                                                                          (force
                                                                                                                                                                             headList
                                                                                                                                                                             (force
                                                                                                                                                                                tailList
                                                                                                                                                                                ds))) ]) ]
                                                                                                                                                              args) ]) ])
                                                                                                                                               (\d ->
                                                                                                                                                  case
                                                                                                                                                    (unConstrData
                                                                                                                                                       d)
                                                                                                                                                    [ (\index
                                                                                                                                                        args ->
                                                                                                                                                         case
                                                                                                                                                           index
                                                                                                                                                           [ (\ds ->
                                                                                                                                                                False)
                                                                                                                                                           , (\ds ->
                                                                                                                                                                True) ]
                                                                                                                                                           args) ]))
                                                                                                                                            (\`$dUnsafeFromData`
                                                                                                                                              d ->
                                                                                                                                               case
                                                                                                                                                 (unConstrData
                                                                                                                                                    d)
                                                                                                                                                 [ (\index
                                                                                                                                                     args ->
                                                                                                                                                      case
                                                                                                                                                        index
                                                                                                                                                        [ (\ds ->
                                                                                                                                                             constr 1
                                                                                                                                                               [  ])
                                                                                                                                                        , (\ds ->
                                                                                                                                                             constr 0
                                                                                                                                                               [ (`$dUnsafeFromData`
                                                                                                                                                                    (force
                                                                                                                                                                       headList
                                                                                                                                                                       ds)) ])
                                                                                                                                                        , (\ds ->
                                                                                                                                                             constr 2
                                                                                                                                                               [  ]) ]
                                                                                                                                                        args) ])) ]
                                                                                                                                     args) ])
                                                                                                                           (go
                                                                                                                              (unListData
                                                                                                                                 (force
                                                                                                                                    headList
                                                                                                                                    l)))
                                                                                                                           (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                                                                              `$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                                                                                              `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                                              (force
                                                                                                                                 headList
                                                                                                                                 l))
                                                                                                                           (cse
                                                                                                                              `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                                              (force
                                                                                                                                 headList
                                                                                                                                 l)))
                                                                                                                        (cse
                                                                                                                           (cse
                                                                                                                              unIData)))
                                                                                                                     (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                                                                        unBData))
                                                                                                                  (\d ->
                                                                                                                     d)
                                                                                                                  (`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData`
                                                                                                                     (force
                                                                                                                        headList
                                                                                                                        (force
                                                                                                                           tailList
                                                                                                                           l))))
                                                                                                               (force
                                                                                                                  tailList
                                                                                                                  l))
                                                                                                            (force
                                                                                                               tailList
                                                                                                               l))
                                                                                                         (force
                                                                                                            tailList
                                                                                                            l))
                                                                                                      (force
                                                                                                         tailList
                                                                                                         l))
                                                                                                   (force
                                                                                                      tailList
                                                                                                      l))
                                                                                                (force
                                                                                                   tailList
                                                                                                   l))
                                                                                             (force
                                                                                                tailList
                                                                                                l))
                                                                                          (force
                                                                                             tailList
                                                                                             l))
                                                                                       (force
                                                                                          tailList
                                                                                          l))
                                                                                    (force
                                                                                       tailList
                                                                                       ds)) ]
                                                                             args) ])
                                                                 , (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                                      (force
                                                                         headList
                                                                         (force
                                                                            tailList
                                                                            ds))) ])
                                                              (\d ->
                                                                 case
                                                                   (unConstrData
                                                                      d)
                                                                   [ (\index
                                                                       args ->
                                                                        case
                                                                          index
                                                                          [ (\ds ->
                                                                               constr 1
                                                                                 [ (unBData
                                                                                      (force
                                                                                         headList
                                                                                         ds)) ])
                                                                          , (\ds ->
                                                                               constr 3
                                                                                 [ (`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData`
                                                                                      (force
                                                                                         headList
                                                                                         ds)) ])
                                                                          , (\ds ->
                                                                               constr 2
                                                                                 [ (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                                                      (force
                                                                                         headList
                                                                                         ds)) ])
                                                                          , (\ds ->
                                                                               constr 0
                                                                                 [ (`$fUnsafeFromDataDCert_$cunsafeFromBuiltinData`
                                                                                      (force
                                                                                         headList
                                                                                         ds)) ]) ]
                                                                          args) ])) ]
                                                       args) ])
                                             [ (\ds
                                                 ds ->
                                                  case
                                                    ds
                                                    [ (\ds
                                                        ds
                                                        ds
                                                        ds
                                                        ds
                                                        ds
                                                        ds
                                                        ds
                                                        ds
                                                        ds
                                                        ds
                                                        ds ->
                                                         force
                                                           ((\`$j` ->
                                                               case
                                                                 ds
                                                                 [ (delay
                                                                      ((\x ->
                                                                          case
                                                                            error
                                                                            [ (\a
                                                                                ds ->
                                                                                 `$j`
                                                                                   a
                                                                                   ds) ])
                                                                         (force
                                                                            trace
                                                                            "PT8"
                                                                            (constr 0
                                                                               [  ]))))
                                                                 , (\x
                                                                     ds ->
                                                                      delay
                                                                        (case
                                                                           x
                                                                           [ (\a
                                                                               ds ->
                                                                                `$j`
                                                                                  a
                                                                                  ds) ])) ])
                                                              (\a
                                                                ds ->
                                                                 force
                                                                   ((\`$j` ->
                                                                       case
                                                                         ds
                                                                         [ (delay
                                                                              (`$j`
                                                                                 ((\x ->
                                                                                     error)
                                                                                    (force
                                                                                       trace
                                                                                       "PT9"
                                                                                       (constr 0
                                                                                          [  ])))))
                                                                         , (\ds
                                                                             as ->
                                                                              delay
                                                                                (`$j`
                                                                                   as)) ])
                                                                      (\rest ->
                                                                         force
                                                                           ((\`$j` ->
                                                                               case
                                                                                 rest
                                                                                 [ (delay
                                                                                      ((\x ->
                                                                                          case
                                                                                            error
                                                                                            [ (\a
                                                                                                ds ->
                                                                                                 `$j`
                                                                                                   a
                                                                                                   ds) ])
                                                                                         (force
                                                                                            trace
                                                                                            "PT8"
                                                                                            (constr 0
                                                                                               [  ]))))
                                                                                 , (\x
                                                                                     ds ->
                                                                                      delay
                                                                                        (case
                                                                                           x
                                                                                           [ (\a
                                                                                               ds ->
                                                                                                `$j`
                                                                                                  a
                                                                                                  ds) ])) ])
                                                                              (\a
                                                                                ds ->
                                                                                 (\obsScriptCred' ->
                                                                                    (\`$fEqStakingCredential_$c==` ->
                                                                                       (\go ->
                                                                                          (\cse ->
                                                                                             case
                                                                                               (cse
                                                                                                  a)
                                                                                               [ (case
                                                                                                    (cse
                                                                                                       a)
                                                                                                    [ (go
                                                                                                         ds)
                                                                                                    , (constr 0
                                                                                                         [  ]) ])
                                                                                               , (constr 0
                                                                                                    [  ]) ])
                                                                                            (`$fEqStakingCredential_$c==`
                                                                                               obsScriptCred'))
                                                                                         ((\s ->
                                                                                             s
                                                                                               s)
                                                                                            (\s
                                                                                              ds ->
                                                                                               case
                                                                                                 ds
                                                                                                 [ ((\x ->
                                                                                                       error)
                                                                                                      (force
                                                                                                         trace
                                                                                                         "not found"
                                                                                                         (constr 0
                                                                                                            [  ])))
                                                                                                 , (\ds
                                                                                                     xs' ->
                                                                                                      case
                                                                                                        ds
                                                                                                        [ (\c'
                                                                                                            i ->
                                                                                                             case
                                                                                                               (`$fEqStakingCredential_$c==`
                                                                                                                  c'
                                                                                                                  obsScriptCred')
                                                                                                               [ (s
                                                                                                                    s
                                                                                                                    xs')
                                                                                                               , (constr 0
                                                                                                                    [  ]) ]) ]) ])))
                                                                                      (\ds
                                                                                        ds ->
                                                                                         case
                                                                                           ds
                                                                                           [ (\l ->
                                                                                                case
                                                                                                  ds
                                                                                                  [ (\r ->
                                                                                                       case
                                                                                                         l
                                                                                                         [ (\l ->
                                                                                                              case
                                                                                                                r
                                                                                                                [ (\r ->
                                                                                                                     equalsByteString
                                                                                                                       l
                                                                                                                       r)
                                                                                                                , (\ipv ->
                                                                                                                     False) ])
                                                                                                         , (\a ->
                                                                                                              case
                                                                                                                r
                                                                                                                [ (\ipv ->
                                                                                                                     False)
                                                                                                                , (\a' ->
                                                                                                                     equalsByteString
                                                                                                                       a
                                                                                                                       a') ]) ])
                                                                                                  , (\ipv
                                                                                                      ipv
                                                                                                      ipv ->
                                                                                                       False) ])
                                                                                           , (\a
                                                                                               b
                                                                                               c ->
                                                                                                case
                                                                                                  ds
                                                                                                  [ (\ipv ->
                                                                                                       False)
                                                                                                  , (\a'
                                                                                                      b'
                                                                                                      c' ->
                                                                                                       case
                                                                                                         (equalsInteger
                                                                                                            a
                                                                                                            a')
                                                                                                         [ False
                                                                                                         , (case
                                                                                                              (equalsInteger
                                                                                                                 b
                                                                                                                 b')
                                                                                                              [ False
                                                                                                              , (equalsInteger
                                                                                                                   c
                                                                                                                   c') ]) ]) ]) ]))
                                                                                   (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                                                      obsScriptCred)))))))) ]) ])
                                          ((\s ->
                                              s s)
                                             (\s
                                               xs ->
                                                case
                                                  xs
                                                  [ (\x
                                                      xs ->
                                                       constr 1
                                                         [ (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                              x)
                                                         , (s s xs) ])
                                                  , (constr 0 []) ])))
                                       ((\s ->
                                           s s)
                                          (\s
                                            xs ->
                                             case
                                               xs
                                               [ (\x
                                                   xs ->
                                                    constr 1
                                                      [ (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                           x)
                                                      , (s s xs) ])
                                               , (constr 0 []) ])))
                                    (\d ->
                                       case
                                         (unConstrData d)
                                         [ (\index
                                             args ->
                                              case
                                                index
                                                [ (\ds ->
                                                     constr 0
                                                       [ (`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData`
                                                            (force headList ds))
                                                       , (`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData`
                                                            (force headList
                                                               (force tailList
                                                                  ds))) ]) ]
                                                args) ]))
                                 (\d ->
                                    case
                                      (unConstrData d)
                                      [ (\index
                                          args ->
                                           case
                                             index
                                             [ (\ds ->
                                                  constr 0
                                                    [ (`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData`
                                                         (force headList ds))
                                                    , (unIData
                                                         (force headList
                                                            (force tailList
                                                               ds))) ]) ]
                                             args) ]))
                              (\d ->
                                 case
                                   (unConstrData d)
                                   [ (\index args ->
                                        case
                                          index
                                          [(\ds -> unBData (force headList ds))]
                                          args) ]))
                           ((\s ->
                               s s)
                              (\s
                                xs ->
                                 case
                                   xs
                                   [ (\x
                                       xs ->
                                        constr 1
                                          [ (`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData`
                                               x)
                                          , (s s xs) ])
                                   , (constr 0 []) ])))
                        (\eta ->
                           case
                             (unConstrData eta)
                             [ (\index
                                 args ->
                                  case
                                    index
                                    [ (\ds ->
                                         (\l ->
                                            (\l ->
                                               (\`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData` ->
                                                  (\cse ->
                                                     constr 0
                                                       [ (case
                                                            (unConstrData
                                                               (force headList
                                                                  ds))
                                                            [ (\index
                                                                args ->
                                                                 case
                                                                   index
                                                                   [ (\ds ->
                                                                        constr 0
                                                                          [ (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                                                               (force
                                                                                  headList
                                                                                  ds))
                                                                          , (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                               `$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                                               (force
                                                                                  headList
                                                                                  (force
                                                                                     tailList
                                                                                     ds))) ]) ]
                                                                   args) ])
                                                       , (cse
                                                            (cse unIData)
                                                            (force headList l))
                                                       , (case
                                                            (unConstrData
                                                               (force headList
                                                                  l))
                                                            [ (\index
                                                                args ->
                                                                 case
                                                                   index
                                                                   [ (\ds ->
                                                                        constr 0
                                                                          [])
                                                                   , (\ds ->
                                                                        constr 2
                                                                          [ (unBData
                                                                               (force
                                                                                  headList
                                                                                  ds)) ])
                                                                   , (\ds ->
                                                                        constr 1
                                                                          [ (force
                                                                               headList
                                                                               ds) ]) ]
                                                                   args) ])
                                                       , (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                            unBData
                                                            (force headList
                                                               (force tailList
                                                                  l))) ])
                                                    (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                       unBData))
                                                 (\`$dUnsafeFromData`
                                                   d ->
                                                    case
                                                      (unConstrData d)
                                                      [ (\index
                                                          args ->
                                                           case
                                                             index
                                                             [ (\ds ->
                                                                  constr 0
                                                                    [ (`$dUnsafeFromData`
                                                                         (force
                                                                            headList
                                                                            ds)) ])
                                                             , (\ds ->
                                                                  constr 1 []) ]
                                                             args) ]))
                                              (force tailList l))
                                           (force tailList ds)) ]
                                    args) ]))
                     (\`$dUnsafeFromData` `$dUnsafeFromData` ->
                        (\go d -> go (unMapData d))
                          ((\s -> s s)
                             (\s xs ->
                                case
                                  xs
                                  [ (\tup tups ->
                                       constr 1
                                         [ (constr 0
                                              [ (`$dUnsafeFromData`
                                                   (case tup [(\l r -> l)]))
                                              , (`$dUnsafeFromData`
                                                   (case tup [(\l r -> r)])) ])
                                         , (s s tups) ])
                                  , (constr 0 []) ]))))
                  ((\s ->
                      s s)
                     (\s
                       xs ->
                        case
                          xs
                          [ (\x
                              xs ->
                               constr 1
                                 [ (`$fUnsafeFromDataDCert_$cunsafeFromBuiltinData`
                                      x)
                                 , (s s xs) ])
                          , (constr 0 []) ])))
               (\d ->
                  case
                    (unConstrData d)
                    [ (\index
                        args ->
                         case
                           index
                           [ (\ds ->
                                constr 2
                                  [ (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                       (force headList ds)) ])
                           , (\ds ->
                                constr 0
                                  [ (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                       (force headList ds)) ])
                           , (\ds ->
                                constr 1
                                  [ (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                       (force headList ds))
                                  , (unBData
                                       (force headList (force tailList ds))) ])
                           , (\ds ->
                                constr 5
                                  [ (unBData (force headList ds))
                                  , (unBData
                                       (force headList (force tailList ds))) ])
                           , (\ds ->
                                constr 6
                                  [ (unBData (force headList ds))
                                  , (unIData
                                       (force headList (force tailList ds))) ])
                           , (\ds -> constr 3 [])
                           , (\ds -> constr 4 []) ]
                           args) ]))
            (\d ->
               case
                 (unConstrData d)
                 [ (\index
                     args ->
                      case
                        index
                        [ (\ds ->
                             constr 0
                               [ (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                    (force headList ds)) ])
                        , (\ds ->
                             (\l ->
                                constr 1
                                  [ (unIData (force headList ds))
                                  , (unIData (force headList l))
                                  , (unIData
                                       (force headList (force tailList l))) ])
                               (force tailList ds)) ]
                        args) ]))
         (\d ->
            case
              (unConstrData d)
              [ (\index args ->
                   case
                     index
                     [ (\ds -> constr 0 [(unBData (force headList ds))])
                     , (\ds -> constr 1 [(unBData (force headList ds))]) ]
                     args) ]))
      ((\s -> s s)
         (\s xs ->
            case
              xs
              [(\x xs -> constr 1 [(unBData x), (s s xs)]), (constr 0 [])]))))
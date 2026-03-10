(program
   1.1.0
   ((\goList ->
       (\goList ->
          (\goList ->
             (\selectByteString
               dim ->
                (\dim ->
                   (\lastRow ->
                      (\go ->
                         (\bytesNeeded ->
                            case
                              (lessThanInteger dim 8)
                              [ (case
                                   (equalsInteger 0 (remainderInteger dim 8))
                                   [ (constr 0 [])
                                   , ((\cse ->
                                         case
                                           (constr 0
                                              [ 0
                                              , 0
                                              , cse
                                              , cse
                                              , cse
                                              , (replicateByte
                                                   bytesNeeded
                                                   255) ])
                                           [go])
                                        (replicateByte bytesNeeded 0)) ])
                              , (constr 0 []) ])
                           (quotientInteger dim 8))
                        ((\s ->
                            s s)
                           (\s
                             selectIx
                             row
                             down
                             left
                             right
                             control ->
                              case
                                (equalsInteger selectIx dim)
                                [ ((\available ->
                                      case
                                        (equalsInteger -1 available)
                                        [ (case
                                             (equalsInteger row lastRow)
                                             [ ((\newRow ->
                                                   (\cse ->
                                                      (\newRight ->
                                                         (\newLeft ->
                                                            (\newDown ->
                                                               (\newControl ->
                                                                  case
                                                                    (case
                                                                       (constr 0
                                                                          [ s
                                                                          , 0
                                                                          , newRow
                                                                          , newDown
                                                                          , newLeft
                                                                          , newRight
                                                                          , newControl ])
                                                                       [s])
                                                                    [ (case
                                                                         (constr 0
                                                                            [ s
                                                                            , (addInteger
                                                                                 1
                                                                                 selectIx)
                                                                            , row
                                                                            , down
                                                                            , left
                                                                            , right
                                                                            , control ])
                                                                         [s])
                                                                    , (\ipv
                                                                        ipv ->
                                                                         constr 1
                                                                           [ (constr 0
                                                                                [ row
                                                                                , available ])
                                                                           , (case
                                                                                (constr 0
                                                                                   [ s
                                                                                   , 0
                                                                                   , newRow
                                                                                   , newDown
                                                                                   , newLeft
                                                                                   , newRight
                                                                                   , newControl ])
                                                                                [ s ]) ]) ])
                                                                 (complementByteString
                                                                    (case
                                                                       (constr 0
                                                                          [ False
                                                                          , newDown
                                                                          , (case
                                                                               (constr 0
                                                                                  [ False
                                                                                  , newLeft
                                                                                  , newRight ])
                                                                               [ orByteString ]) ])
                                                                       [ orByteString ])))
                                                              (case
                                                                 (constr 0
                                                                    [ down
                                                                    , (goList
                                                                         cse)
                                                                    , True ])
                                                                 [writeBits]))
                                                           (shiftByteString
                                                              (case
                                                                 (constr 0
                                                                    [ left
                                                                    , (goList
                                                                         cse)
                                                                    , True ])
                                                                 [writeBits])
                                                              1))
                                                        (shiftByteString
                                                           (case
                                                              (constr 0
                                                                 [ right
                                                                 , (goList cse)
                                                                 , True ])
                                                              [writeBits])
                                                           -1))
                                                     (constr 1
                                                        [ available
                                                        , (constr 0 []) ]))
                                                  (addInteger 1 row))
                                             , (constr 1
                                                  [ (constr 0 [row, available])
                                                  , (constr 0 []) ]) ])
                                        , (constr 0 []) ])
                                     (selectByteString selectIx control))
                                , (constr 0 []) ])))
                     (subtractInteger dim 1))
                  (unIData dim))
               ((\s -> s s)
                  (\s which bs ->
                     case
                       (lessThanEqualsInteger which 0)
                       [ ((\i ->
                             case
                               (equalsInteger -1 i)
                               [ ((\cse ->
                                     addInteger
                                       cse
                                       (findFirstSetBit
                                          (shiftByteString
                                             bs
                                             (subtractInteger 0 cse))))
                                    (addInteger 1 i))
                               , -1 ])
                            ((\x -> s s x) (subtractInteger which 1) bs))
                       , (findFirstSetBit bs) ])))
            ((\s -> s s)
               (\s ds -> case ds [[], (\d ds -> force mkCons d (s s ds))])))
         ((\s -> s s)
            (\s ds -> case ds [[], (\d ds -> force mkCons d (s s ds))])))
      ((\s -> s s) (\s ds -> case ds [[], (\d ds -> force mkCons d (s s ds))]))
      (I 8)))
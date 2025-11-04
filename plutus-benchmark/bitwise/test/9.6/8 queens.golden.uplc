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
                                         go
                                           0
                                           0
                                           cse
                                           cse
                                           cse
                                           (replicateByte bytesNeeded 255))
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
                                                                    (s
                                                                       s
                                                                       0
                                                                       newRow
                                                                       newDown
                                                                       newLeft
                                                                       newRight
                                                                       newControl)
                                                                    [ (s
                                                                         s
                                                                         (addInteger
                                                                            1
                                                                            selectIx)
                                                                         row
                                                                         down
                                                                         left
                                                                         right
                                                                         control)
                                                                    , (\ipv
                                                                        ipv ->
                                                                         constr 1
                                                                           [ (constr 0
                                                                                [ row
                                                                                , available ])
                                                                           , (s
                                                                                s
                                                                                0
                                                                                newRow
                                                                                newDown
                                                                                newLeft
                                                                                newRight
                                                                                newControl) ]) ])
                                                                 (complementByteString
                                                                    (orByteString
                                                                       False
                                                                       newDown
                                                                       (orByteString
                                                                          False
                                                                          newLeft
                                                                          newRight))))
                                                              (writeBits
                                                                 down
                                                                 (goList cse)
                                                                 True))
                                                           (shiftByteString
                                                              (writeBits
                                                                 left
                                                                 (goList cse)
                                                                 True)
                                                              1))
                                                        (shiftByteString
                                                           (writeBits
                                                              right
                                                              (goList cse)
                                                              True)
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
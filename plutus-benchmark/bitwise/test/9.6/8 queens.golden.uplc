(program
   1.1.0
   ((\goList ->
       (\goList ->
          (\goList ->
             (\selectByteString
               dim ->
                (\cse ->
                   (\lastRow ->
                      (\go ->
                         (\bytesNeeded ->
                            case
                              (lessThanInteger cse 8)
                              [ (case
                                   (equalsInteger 0 (remainderInteger cse 8))
                                   [ (constr 0 [])
                                   , ((\cse ->
                                         (\cse -> go 0 0 cse cse cse (cse 255))
                                           (cse 0))
                                        (replicateByte bytesNeeded)) ])
                              , (constr 0 []) ])
                           (quotientInteger cse 8))
                        ((\cse ->
                            cse cse)
                           (\s
                             selectIx
                             row
                             down
                             left
                             right
                             control ->
                              case
                                (equalsInteger selectIx cse)
                                [ ((\cse ->
                                      case
                                        (equalsInteger -1 cse)
                                        [ (case
                                             (equalsInteger row lastRow)
                                             [ ((\cse ->
                                                   (\newRow ->
                                                      (\cse ->
                                                         case
                                                           (s
                                                              s
                                                              0
                                                              newRow
                                                              (writeBits
                                                                 down
                                                                 (goList cse)
                                                                 True)
                                                              (shiftByteString
                                                                 (writeBits
                                                                    left
                                                                    (goList cse)
                                                                    True)
                                                                 1)
                                                              (shiftByteString
                                                                 (writeBits
                                                                    right
                                                                    (goList cse)
                                                                    True)
                                                                 -1)
                                                              (complementByteString
                                                                 (orByteString
                                                                    False
                                                                    (writeBits
                                                                       down
                                                                       (goList
                                                                          cse)
                                                                       True)
                                                                    (orByteString
                                                                       False
                                                                       (shiftByteString
                                                                          (writeBits
                                                                             left
                                                                             (goList
                                                                                cse)
                                                                             True)
                                                                          1)
                                                                       (shiftByteString
                                                                          (writeBits
                                                                             right
                                                                             (goList
                                                                                cse)
                                                                             True)
                                                                          -1)))))
                                                           [ (s
                                                                s
                                                                (cse selectIx)
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
                                                                       , cse ])
                                                                  , (s
                                                                       s
                                                                       0
                                                                       newRow
                                                                       (writeBits
                                                                          down
                                                                          (goList
                                                                             cse)
                                                                          True)
                                                                       (shiftByteString
                                                                          (writeBits
                                                                             left
                                                                             (goList
                                                                                cse)
                                                                             True)
                                                                          1)
                                                                       (shiftByteString
                                                                          (writeBits
                                                                             right
                                                                             (goList
                                                                                cse)
                                                                             True)
                                                                          -1)
                                                                       (complementByteString
                                                                          (orByteString
                                                                             False
                                                                             (writeBits
                                                                                down
                                                                                (goList
                                                                                   cse)
                                                                                True)
                                                                             (orByteString
                                                                                False
                                                                                (shiftByteString
                                                                                   (writeBits
                                                                                      left
                                                                                      (goList
                                                                                         cse)
                                                                                      True)
                                                                                   1)
                                                                                (shiftByteString
                                                                                   (writeBits
                                                                                      right
                                                                                      (goList
                                                                                         cse)
                                                                                      True)
                                                                                   -1))))) ]) ])
                                                        (constr 1
                                                           [ cse
                                                           , (constr 0 []) ]))
                                                     (cse row))
                                                  (addInteger 1))
                                             , (constr 1
                                                  [ (constr 0 [row, cse])
                                                  , (constr 0 []) ]) ])
                                        , (constr 0 []) ])
                                     (selectByteString selectIx control))
                                , (constr 0 []) ])))
                     (subtractInteger cse 1))
                  (unIData dim))
               ((\cse -> cse cse)
                  (\s which bs ->
                     case
                       (lessThanEqualsInteger which 0)
                       [ ((\cse ->
                             case
                               (equalsInteger -1 cse)
                               [ ((\cse ->
                                     addInteger
                                       cse
                                       (findFirstSetBit
                                          (shiftByteString
                                             bs
                                             (subtractInteger 0 cse))))
                                    (addInteger 1 cse))
                               , -1 ])
                            ((\x -> s s x) (subtractInteger which 1) bs))
                       , (findFirstSetBit bs) ])))
            ((\cse -> cse cse)
               (\s ds -> case ds [[], (\d ds -> force mkCons d (s s ds))])))
         ((\cse -> cse cse)
            (\s ds -> case ds [[], (\d ds -> force mkCons d (s s ds))])))
      ((\cse -> cse cse)
         (\s ds -> case ds [[], (\d ds -> force mkCons d (s s ds))]))
      (I 8)))
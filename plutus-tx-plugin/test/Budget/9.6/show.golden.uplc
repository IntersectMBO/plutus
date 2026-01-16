(program
   1.1.0
   ((\go ->
       (\go ->
          (\`$fShowBuiltinByteString_$cshowsPrec` ->
             (\go ->
                (\`$dmenumFromTo_$cenumFromTo` ->
                   (\go ->
                      (\go ->
                         (\concatBuiltinStrings ->
                            (\cse ->
                               (\cse ->
                                  (\cse ->
                                     (\cse ->
                                        (\cse ->
                                           (\cse ->
                                              (\cse ->
                                                 (\cse ->
                                                    multiplyInteger
                                                      2
                                                      (cse
                                                         (concatBuiltinStrings
                                                            (constr 1
                                                               [ "("
                                                               , (case
                                                                    cse
                                                                    [ (\v v ->
                                                                         v) ]
                                                                    0
                                                                    cse
                                                                    (constr 1
                                                                       [ ","
                                                                       , (case
                                                                            cse
                                                                            [ (\v
                                                                                v ->
                                                                                 v) ]
                                                                            0
                                                                            cse
                                                                            (constr 1
                                                                               [ ","
                                                                               , (case
                                                                                    cse
                                                                                    [ (\v
                                                                                        v ->
                                                                                         v) ]
                                                                                    0
                                                                                    cse
                                                                                    (constr 1
                                                                                       [ ","
                                                                                       , (case
                                                                                            cse
                                                                                            [ (\v
                                                                                                v ->
                                                                                                 v) ]
                                                                                            0
                                                                                            cse
                                                                                            (constr 1
                                                                                               [ ","
                                                                                               , (case
                                                                                                    cse
                                                                                                    [ (\v
                                                                                                        v ->
                                                                                                         v) ]
                                                                                                    0
                                                                                                    cse
                                                                                                    (constr 1
                                                                                                       [ ")"
                                                                                                       , (constr 0
                                                                                                            [  ]) ])) ])) ])) ])) ])) ]))
                                                         cse))
                                                   (cse
                                                      (concatBuiltinStrings
                                                         ((\showElem ->
                                                             (\go
                                                               eta ->
                                                                constr 1
                                                                  [ "["
                                                                  , (showElem
                                                                       cse
                                                                       (go
                                                                          (constr 1
                                                                             [ cse
                                                                             , (constr 1
                                                                                  [ cse
                                                                                  , (constr 1
                                                                                       [ cse
                                                                                       , (constr 0
                                                                                            [  ]) ]) ]) ])
                                                                          (constr 1
                                                                             [ "]"
                                                                             , eta ]))) ])
                                                               ((\cse ->
                                                                   cse cse)
                                                                  (\s
                                                                    ds ->
                                                                     case
                                                                       ds
                                                                       [ (\x ->
                                                                            x)
                                                                       , (\x
                                                                           xs ->
                                                                            (\acc
                                                                              eta ->
                                                                               constr 1
                                                                                 [ ","
                                                                                 , (showElem
                                                                                      x
                                                                                      (acc
                                                                                         eta)) ])
                                                                              (s
                                                                                 s
                                                                                 xs)) ])))
                                                            (case
                                                               cse
                                                               [(\v v -> v)]
                                                               0)
                                                            (constr 0 [])))
                                                      cse))
                                                (cse
                                                   (case
                                                      (lessThanEqualsInteger
                                                         cse
                                                         0)
                                                      ["True", "False"])
                                                   cse))
                                             (constr 0
                                                [ `$fShowBuiltinByteString_$cshowsPrec`
                                                , cse ]))
                                          (cse
                                             (concatBuiltinStrings
                                                (go
                                                   (`$dmenumFromTo_$cenumFromTo`
                                                      0
                                                      17)
                                                   (constr 0 [])))
                                             cse))
                                       (cse "This is an example" cse))
                                    (cse (cse -1234567890) -1234567890))
                                 (\x ->
                                    concatBuiltinStrings
                                      (`$fShowBuiltinByteString_$cshowsPrec`
                                         0
                                         x
                                         (constr 0 []))))
                              (force trace))
                           ((\cse -> cse cse)
                              (\s ds ->
                                 case
                                   ds
                                   [ ""
                                   , (\x ds ->
                                        case
                                          ds
                                          [ x
                                          , (\ipv ipv ->
                                               case
                                                 ((\cse ->
                                                     case
                                                       (lessThanEqualsInteger
                                                          cse
                                                          0)
                                                       [ (go cse ds)
                                                       , (constr 0
                                                            [ (constr 0 [])
                                                            , ds ]) ])
                                                    (divideInteger (go ds) 2))
                                                 [ (\ipv ipv ->
                                                      (\cse ->
                                                         appendString
                                                           (cse ipv)
                                                           (cse ipv))
                                                        (s s)) ]) ]) ])))
                        ((\cse -> cse cse)
                           (\s ds ->
                              case ds [0, (\ds xs -> addInteger 1 (s s xs))])))
                     ((\cse -> cse cse)
                        (\s ds ds ->
                           case
                             ds
                             [ (constr 0 [(constr 0 []), (constr 0 [])])
                             , (\y ys ->
                                  case
                                    (equalsInteger 1 ds)
                                    [ (case
                                         ((\x -> s s x)
                                            (subtractInteger ds 1)
                                            ys)
                                         [ (\zs ws ->
                                              constr 0
                                                [(constr 1 [y, zs]), ws]) ])
                                    , (constr 0
                                         [ (constr 1 [y, (constr 0 [])])
                                         , ys ]) ]) ])))
                  ((\cse -> cse cse)
                     (\s x lim ->
                        case
                          (lessThanEqualsInteger x lim)
                          [ (constr 0 [])
                          , (constr 1
                               [x, ((\x -> s s x) (addInteger 1 x) lim)]) ])))
               ((\cse ->
                   cse cse)
                  (\s
                    ds ->
                     case
                       ds
                       [ (\x -> x)
                       , (\x
                           xs ->
                            (\acc
                              eta ->
                               (\eta ->
                                  (\cse ->
                                     (\cse ->
                                        cse
                                          (divideInteger cse 16)
                                          (cse (modInteger cse 16) eta))
                                       (indexByteString
                                          #5468697320697320616e206578616d706c65
                                          x))
                                    (\x ->
                                       case
                                         (lessThanEqualsInteger x 9)
                                         [ (case
                                              (equalsInteger 10 x)
                                              [ (case
                                                   (equalsInteger 11 x)
                                                   [ (case
                                                        (equalsInteger 12 x)
                                                        [ (case
                                                             (equalsInteger
                                                                13
                                                                x)
                                                             [ (case
                                                                  (equalsInteger
                                                                     14
                                                                     x)
                                                                  [ (case
                                                                       (equalsInteger
                                                                          15
                                                                          x)
                                                                       [ (\ds ->
                                                                            constr 1
                                                                              [ "<invalid byte>"
                                                                              , ds ])
                                                                       , (\ds ->
                                                                            constr 1
                                                                              [ "f"
                                                                              , ds ]) ])
                                                                  , (\ds ->
                                                                       constr 1
                                                                         [ "e"
                                                                         , ds ]) ])
                                                             , (\ds ->
                                                                  constr 1
                                                                    [ "d"
                                                                    , ds ]) ])
                                                        , (\ds ->
                                                             constr 1
                                                               ["c", ds]) ])
                                                   , (\ds ->
                                                        constr 1 ["b", ds]) ])
                                              , (\ds -> constr 1 ["a", ds]) ])
                                         , (`$fShowBuiltinByteString_$cshowsPrec`
                                              0
                                              x) ]))
                                 (acc eta))
                              (s s xs)) ])))
            ((\cse -> cse cse)
               (\s p n ->
                  case
                    (lessThanInteger n 0)
                    [ (go (go (constr 0 []) n))
                    , (\eta ->
                         constr 1 ["-", (s s p (subtractInteger 0 n) eta)]) ])))
         ((\cse ->
             cse cse)
            (\s
              ds ->
               case
                 ds
                 [ (\x -> x)
                 , (\x
                     xs ->
                      (\acc
                        eta ->
                         constr 1
                           [ (case
                                (equalsInteger 0 x)
                                [ (case
                                     (equalsInteger 1 x)
                                     [ (case
                                          (equalsInteger 2 x)
                                          [ (case
                                               (equalsInteger 3 x)
                                               [ (case
                                                    (equalsInteger 4 x)
                                                    [ (case
                                                         (equalsInteger 5 x)
                                                         [ (case
                                                              (equalsInteger
                                                                 6
                                                                 x)
                                                              [ (case
                                                                   (equalsInteger
                                                                      7
                                                                      x)
                                                                   [ (case
                                                                        (equalsInteger
                                                                           8
                                                                           x)
                                                                        [ (case
                                                                             (equalsInteger
                                                                                9
                                                                                x)
                                                                             [ "<invalid digit>"
                                                                             , "9" ])
                                                                        , "8" ])
                                                                   , "7" ])
                                                              , "6" ])
                                                         , "5" ])
                                                    , "4" ])
                                               , "3" ])
                                          , "2" ])
                                     , "1" ])
                                , "0" ])
                           , (acc eta) ])
                        (s s xs)) ])))
      ((\cse -> cse cse)
         (\s acc n ->
            (\cse ->
               case
                 (equalsInteger 0 cse)
                 [ ((\x -> s s x) (constr 1 [(remainderInteger n 10), acc]) cse)
                 , (constr 1 [(remainderInteger n 10), acc]) ])
              (quotientInteger n 10)))))
(program
   1.1.0
   (\d ->
      case
        (unConstrData d)
        [ (\idx args ->
             case
               idx
               [ (force headList args)
               , (force headList args)
               , (case
                    args
                    [ (\hd tl ->
                         (\`$mInts` ->
                            `$mInts`
                              hd
                              (\x y z w ->
                                 case
                                   (constr 0
                                      [ (force headList tl)
                                      , (\x y z w ->
                                           constrData
                                             0
                                             (force mkCons
                                                (iData (addInteger x x))
                                                (force mkCons
                                                   (iData (addInteger y y))
                                                   (force mkCons
                                                      (iData (addInteger z z))
                                                      (force mkCons
                                                         (iData
                                                            (addInteger w w))
                                                         [])))))
                                      , (\void ->
                                           (\cse -> case cse [cse]) error) ])
                                   [`$mInts`]))
                           (\scrut cont fail ->
                              (\l ->
                                 (\l ->
                                    (\l ->
                                       case
                                         (constr 0
                                            [ (unIData (force headList l))
                                            , (unIData (force headList l))
                                            , (unIData (force headList l))
                                            , (unIData
                                                 (force headList
                                                    (force tailList l))) ])
                                         [cont])
                                      (force tailList l))
                                   (force tailList l))
                                (case (unConstrData scrut) [(\l r -> r)]))
                           (\void -> (\cse -> case cse [cse]) error)) ]) ]) ]))
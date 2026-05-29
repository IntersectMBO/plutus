let
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r ->
        \(z : r) (f : a -> list a -> r) (xs : list a) ->
          chooseList
            {a}
            {all dead. r}
            xs
            (/\dead -> z)
            (/\dead -> f (headList {a} xs) (tailList {a} xs))
            {r}
in
\(bd : data) ->
  letrec
    !goOuter :
       list (pair data data) -> integer
      = caseList'
          {pair data data}
          {integer}
          0
          (\(hd : pair data data) ->
             ifThenElse
               {all dead. list (pair data data) -> integer}
               (equalsByteString
                  #706f6c6963795f30355f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                  (unBData (fstPair {data} {data} hd)))
               (/\dead ->
                  \(ds : list (pair data data)) ->
                    (letrec
                        !goInner :
                           list (pair data data) -> integer
                          = caseList'
                              {pair data data}
                              {integer}
                              0
                              (\(hd : pair data data) ->
                                 ifThenElse
                                   {all dead. list (pair data data) -> integer}
                                   (equalsByteString
                                      #746f6b656e5f30355f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                                      (unBData (fstPair {data} {data} hd)))
                                   (/\dead ->
                                      \(ds : list (pair data data)) ->
                                        unIData (sndPair {data} {data} hd))
                                   (/\dead -> goInner)
                                   {all dead. dead})
                      in
                      goInner)
                      (unMapData (sndPair {data} {data} hd)))
               (/\dead -> goOuter)
               {all dead. dead})
  in
  goOuter (unMapData bd)
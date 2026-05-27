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
letrec
  ~goInner :
     list (pair data data) -> integer
    = caseList'
        {pair data data}
        {integer}
        0
        (\(hd : pair data data) ->
           ifThenElse
             {all dead. list (pair data data) -> integer}
             (equalsByteString
                #746f6b656e5f30315f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                (unBData (fstPair {data} {data} hd)))
             (/\dead ->
                \(ds : list (pair data data)) ->
                  unIData (sndPair {data} {data} hd))
             (/\dead -> goInner)
             {all dead. dead})
in
\(bd : data) ->
  let
    !ds :
       (\k a -> list (pair data data))
         bytestring
         ((\k a -> list (pair data data)) bytestring integer)
      = unMapData bd
  in
  letrec
    !goOuter : list (pair data data) -> integer
      = caseList'
          {pair data data}
          {integer}
          0
          (\(hd : pair data data) ->
             ifThenElse
               {all dead. list (pair data data) -> integer}
               (equalsByteString
                  #706f6c6963795f30315f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                  (unBData (fstPair {data} {data} hd)))
               (/\dead ->
                  \(ds : list (pair data data)) ->
                    goInner (unMapData (sndPair {data} {data} hd)))
               (/\dead -> goOuter)
               {all dead. dead})
  in
  goOuter ds
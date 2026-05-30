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
  !go : list (pair data data) -> list (pair data data) -> list (pair data data)
    = \(lA : list (pair data data)) (lB : list (pair data data)) ->
        caseList'
          {pair data data}
          {list (pair data data)}
          lB
          (\(hdA : pair data data) (tlA : list (pair data data)) ->
             caseList'
               {pair data data}
               {list (pair data data)}
               lA
               (\(hdB : pair data data) (tlB : list (pair data data)) ->
                  let
                    !keyB : bytestring = unBData (fstPair {data} {data} hdB)
                    !keyA : bytestring = unBData (fstPair {data} {data} hdA)
                  in
                  ifThenElse
                    {all dead. list (pair data data)}
                    (equalsByteString keyA keyB)
                    (/\dead ->
                       mkCons
                         {pair data data}
                         (mkPairData
                            (fstPair {data} {data} hdA)
                            (iData
                               (addInteger
                                  (unIData (sndPair {data} {data} hdA))
                                  (unIData (sndPair {data} {data} hdB)))))
                         (go tlA tlB))
                    (/\dead ->
                       ifThenElse
                         {all dead. list (pair data data)}
                         (lessThanByteString keyA keyB)
                         (/\dead -> mkCons {pair data data} hdA (go tlA lB))
                         (/\dead -> mkCons {pair data data} hdB (go lA tlB))
                         {all dead. dead})
                    {all dead. dead})
               lB)
          lA
in
letrec
  !go : list (pair data data) -> list (pair data data) -> list (pair data data)
    = \(lA : list (pair data data)) (lB : list (pair data data)) ->
        caseList'
          {pair data data}
          {list (pair data data)}
          lB
          (\(hdA : pair data data) (tlA : list (pair data data)) ->
             caseList'
               {pair data data}
               {list (pair data data)}
               lA
               (\(hdB : pair data data) (tlB : list (pair data data)) ->
                  let
                    !keyB : bytestring = unBData (fstPair {data} {data} hdB)
                    !keyA : bytestring = unBData (fstPair {data} {data} hdA)
                  in
                  ifThenElse
                    {all dead. list (pair data data)}
                    (equalsByteString keyA keyB)
                    (/\dead ->
                       mkCons
                         {pair data data}
                         (mkPairData
                            (fstPair {data} {data} hdA)
                            (mapData
                               (go
                                  (unMapData (sndPair {data} {data} hdA))
                                  (unMapData (sndPair {data} {data} hdB)))))
                         (go tlA tlB))
                    (/\dead ->
                       ifThenElse
                         {all dead. list (pair data data)}
                         (lessThanByteString keyA keyB)
                         (/\dead -> mkCons {pair data data} hdA (go tlA lB))
                         (/\dead -> mkCons {pair data data} hdB (go lA tlB))
                         {all dead. dead})
                    {all dead. dead})
               lB)
          lA
in
\(bd : data) (bd : data) -> mapData (go (unMapData bd) (unMapData bd))
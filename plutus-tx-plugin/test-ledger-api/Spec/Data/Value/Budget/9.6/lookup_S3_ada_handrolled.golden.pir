letrec
  !goInner : list (pair data data) -> integer
    = \(list : list (pair data data)) ->
        case
          integer
          list
          [ (\(hd : pair data data) ->
               case
                 (all dead. list (pair data data) -> integer)
                 (equalsByteString
                    #
                    (unBData (case data hd [(\(l : data) (r : data) -> l)])))
                 [ (/\dead -> goInner)
                 , (/\dead ->
                      \(ds : list (pair data data)) ->
                        unIData
                          (case data hd [(\(l : data) (r : data) -> r)])) ]
                 {all dead. dead})
          , 0 ]
in
letrec
  !goOuter : list (pair data data) -> integer
    = \(list : list (pair data data)) ->
        case
          integer
          list
          [ (\(hd : pair data data) ->
               case
                 (all dead. list (pair data data) -> integer)
                 (equalsByteString
                    #
                    (unBData (case data hd [(\(l : data) (r : data) -> l)])))
                 [ (/\dead -> goOuter)
                 , (/\dead ->
                      \(ds : list (pair data data)) ->
                        goInner
                          (unMapData
                             (case data hd [(\(l : data) (r : data) -> r)]))) ]
                 {all dead. dead})
          , 0 ]
in
\(bd : data) -> goOuter (unMapData bd)
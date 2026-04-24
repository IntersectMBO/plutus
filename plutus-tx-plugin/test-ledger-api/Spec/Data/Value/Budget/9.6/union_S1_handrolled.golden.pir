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
let
  !filterMissingOuter :
     list (pair data data) -> list (pair data data) -> list (pair data data)
    = \(l : list (pair data data)) (l : list (pair data data)) ->
        letrec
          !go : list (pair data data) -> list (pair data data)
            = \(list : list (pair data data)) ->
                case
                  (list (pair data data))
                  list
                  [ (\(hd : pair data data) ->
                       case
                         (list (pair data data) -> list (pair data data))
                         ((let
                              !k : data
                                = case data hd [(\(l : data) (r : data) -> l)]
                            in
                            letrec
                              !go : list (pair data data) -> bool
                                = \(xs : list (pair data data)) ->
                                    case
                                      bool
                                      xs
                                      [ (\(hd : pair data data) ->
                                           case
                                             (all dead.
                                                list (pair data data) -> bool)
                                             (equalsData
                                                k
                                                (case
                                                   data
                                                   hd
                                                   [ (\(l : data) (r : data) ->
                                                        l) ]))
                                             [ (/\dead -> go)
                                             , (/\dead ->
                                                  \(ds :
                                                      list (pair data data)) ->
                                                    True) ]
                                             {all dead. dead})
                                      , False ]
                            in
                            go)
                            l)
                         [ (\(tl : list (pair data data)) ->
                              mkCons {pair data data} hd (go tl))
                         , (\(tl : list (pair data data)) -> go tl) ])
                  , [] ]
        in
        go l
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !lookupKeyInMap : data -> list (pair data data) -> Maybe data
    = \(k : data) ->
        letrec
          !go : list (pair data data) -> Maybe data
            = \(xs : list (pair data data)) ->
                case
                  (Maybe data)
                  xs
                  [ (\(hd : pair data data) ->
                       case
                         (all dead. list (pair data data) -> Maybe data)
                         (equalsData
                            k
                            (case data hd [(\(l : data) (r : data) -> l)]))
                         [ (/\dead -> go)
                         , (/\dead ->
                              \(ds : list (pair data data)) ->
                                Just
                                  {data}
                                  (case
                                     data
                                     hd
                                     [(\(l : data) (r : data) -> r)])) ]
                         {all dead. dead})
                  , (Nothing {data}) ]
        in
        go
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
in
\(bd : data)
 (bd : data) ->
  let
    !bd :
       data
      = let
        !outer : list (pair data data) = unMapData bd
      in
      letrec
        !goOuter :
           list (pair data data) -> list (pair data data)
          = \(list : list (pair data data)) ->
              case
                (list (pair data data))
                list
                [ (\(hd : pair data data) ->
                     let
                       ~csData : data
                         = case data hd [(\(l : data) (r : data) -> l)]
                     in
                     \(tl : list (pair data data)) ->
                       mkCons
                         {pair data data}
                         (mkPairData
                            csData
                            (Maybe_match
                               {data}
                               (lookupKeyInMap csData outer)
                               {all dead. data}
                               (\(inner2Data : data) ->
                                  /\dead ->
                                    let
                                      !i : list (pair data data)
                                        = unMapData inner2Data
                                    in
                                    letrec
                                      !goInner :
                                         list (pair data data) ->
                                         list (pair data data)
                                        = \(list : list (pair data data)) ->
                                            case
                                              (list (pair data data))
                                              list
                                              [ (\(hd : pair data data) ->
                                                   let
                                                     ~tnData : data
                                                       = case
                                                           data
                                                           hd
                                                           [ (\(l : data)
                                                               (r : data) ->
                                                                l) ]
                                                   in
                                                   \(tl :
                                                       list (pair data data)) ->
                                                     mkCons
                                                       {pair data data}
                                                       (mkPairData
                                                          tnData
                                                          (iData
                                                             (Maybe_match
                                                                {data}
                                                                (lookupKeyInMap
                                                                   tnData
                                                                   i)
                                                                {all dead.
                                                                   integer}
                                                                (\(amt2Data :
                                                                     data) ->
                                                                   /\dead ->
                                                                     addInteger
                                                                       (unIData
                                                                          (case
                                                                             data
                                                                             hd
                                                                             [ (\(l :
                                                                                    data)
                                                                                 (r :
                                                                                    data) ->
                                                                                  r) ]))
                                                                       (unIData
                                                                          amt2Data))
                                                                (/\dead ->
                                                                   unIData
                                                                     (case
                                                                        data
                                                                        hd
                                                                        [ (\(l :
                                                                               data)
                                                                            (r :
                                                                               data) ->
                                                                             r) ]))
                                                                {all dead.
                                                                   dead})))
                                                       (goInner tl))
                                              , [] ]
                                    in
                                    let
                                      !i : list (pair data data)
                                        = unMapData
                                            (case
                                               data
                                               hd
                                               [(\(l : data) (r : data) -> r)])
                                    in
                                    mapData
                                      (letrec
                                        !go :
                                           list (pair data data) ->
                                           list (pair data data)
                                          = caseList'
                                              {pair data data}
                                              {list (pair data data)}
                                              (filterMissingOuter i i)
                                              (\(hd : pair data data)
                                                (tl : list (pair data data)) ->
                                                 mkCons
                                                   {pair data data}
                                                   hd
                                                   (go tl))
                                      in
                                      go (goInner i)))
                               (/\dead ->
                                  case data hd [(\(l : data) (r : data) -> r)])
                               {all dead. dead}))
                         (goOuter tl))
                , [] ]
      in
      let
        !outer : list (pair data data) = unMapData bd
      in
      mapData
        (letrec
          !go : list (pair data data) -> list (pair data data)
            = caseList'
                {pair data data}
                {list (pair data data)}
                (filterMissingOuter outer outer)
                (\(hd : pair data data) (tl : list (pair data data)) ->
                   mkCons {pair data data} hd (go tl))
        in
        go (goOuter outer))
  in
  goOuter (unMapData bd)
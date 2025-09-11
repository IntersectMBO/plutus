letrec
  !go : list (pair data data) -> integer
    = \(xs : list (pair data data)) ->
        case
          integer
          xs
          [ (\(hd : pair data data) (eta : list (pair data data)) ->
               addInteger
                 (unIData (case data hd [(\(l : data) (r : data) -> r)]))
                 (go eta))
          , 0 ]
in
let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
\(value :
    (\k a -> list (pair data data))
      bytestring
      ((\k a -> list (pair data data)) bytestring integer))
 (cur : bytestring) ->
  Maybe_match
    {data}
    (let
      !k : data = bData cur
    in
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
                              (case data hd [(\(l : data) (r : data) -> r)])) ]
                     {all dead. dead})
              , (Nothing {data}) ]
    in
    go value)
    {integer}
    (\(a : data) -> go (unMapData a))
    0
let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !lookup' : data -> list (pair data data) -> Maybe data
    = \(k : data) (m : list (pair data data)) ->
        (letrec
            !go : list (pair data data) -> Maybe data
              = (let
                    a = pair data data
                  in
                  /\r ->
                    \(z : r) (f : a -> list a -> r) (xs : list a) ->
                      case r xs [f, z])
                  {Maybe data}
                  (Nothing {data})
                  (\(hd : pair data data) ->
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
          in
          go)
          m
in
\(bd : data) ->
  let
    !value :
       (\k a -> list (pair data data))
         bytestring
         ((\k a -> list (pair data data)) bytestring integer)
      = unMapData bd
  in
  Maybe_match
    {data}
    (lookup'
       (B #706f6c6963795f31305f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f)
       value)
    {integer}
    (\(a : data) ->
       let
         !m : list (pair data data) = unMapData a
       in
       Maybe_match
         {data}
         (lookup'
            (B #746f6b656e5f31305f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f)
            m)
         {integer}
         (\(a : data) -> unIData a)
         0)
    0
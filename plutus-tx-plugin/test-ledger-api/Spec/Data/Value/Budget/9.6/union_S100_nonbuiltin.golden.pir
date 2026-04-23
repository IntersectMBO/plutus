let
  !`$fToDataInteger_$ctoBuiltinData` : integer -> data
    = \(i : integer) -> iData i
  data (These :: * -> * -> *) a b | These_match where
    That : b -> These a b
    These : a -> b -> These a b
    This : a -> These a b
  !`$fToDataThese_$ctoBuiltinData` :
     all a b. (\a -> a -> data) a -> (\a -> a -> data) b -> These a b -> data
    = /\a b ->
        \(`$dToData` : (\a -> a -> data) a)
         (`$dToData` : (\a -> a -> data) b)
         (ds : These a b) ->
          These_match
            {a}
            {b}
            ds
            {data}
            (\(arg : b) -> constrData 1 (mkCons {data} (`$dToData` arg) []))
            (\(arg : a) (arg : b) ->
               constrData
                 2
                 (mkCons
                    {data}
                    (`$dToData` arg)
                    (mkCons {data} (`$dToData` arg) [])))
            (\(arg : a) -> constrData 0 (mkCons {data} (`$dToData` arg) []))
  ~`$dToData` : These integer integer -> data
    = `$fToDataThese_$ctoBuiltinData`
        {integer}
        {integer}
        `$fToDataInteger_$ctoBuiltinData`
        `$fToDataInteger_$ctoBuiltinData`
  !`$fUnsafeFromDataThese_$cunsafeFromBuiltinData` :
     all a b. (\a -> data -> a) a -> (\a -> data -> a) b -> data -> These a b
    = /\a b ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a)
         (`$dUnsafeFromData` : (\a -> data -> a) b)
         (d : data) ->
          (let
              b = list data
            in
            /\r ->
              \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
            {These a b}
            (unConstrData d)
            (\(index : integer) (args : list data) ->
               case
                 (list data -> These a b)
                 index
                 [ (\(ds : list data) ->
                      This {a} {b} (`$dUnsafeFromData` (headList {data} ds)))
                 , (\(ds : list data) ->
                      That {a} {b} (`$dUnsafeFromData` (headList {data} ds)))
                 , (\(ds : list data) ->
                      These
                        {a}
                        {b}
                        (`$dUnsafeFromData` (headList {data} ds))
                        (`$dUnsafeFromData`
                           (headList {data} (tailList {data} ds)))) ]
                 args)
  !`$fToDataMap_$ctoBuiltinData` :
     all k a. (\k a -> list (pair data data)) k a -> data
    = /\k a -> \(ds : (\k a -> list (pair data data)) k a) -> mapData ds
  !map :
     all k a b.
       (\a -> data -> a) a ->
       (\a -> a -> data) b ->
       (a -> b) ->
       (\k a -> list (pair data data)) k a ->
       (\k a -> list (pair data data)) k b
    = /\k a b ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a)
         (`$dToData` : (\a -> a -> data) b)
         (f : a -> b) ->
          letrec
            !go : list (pair data data) -> list (pair data data)
              = \(xs : list (pair data data)) ->
                  case
                    (list (pair data data))
                    xs
                    [ (\(hd : pair data data) (eta : list (pair data data)) ->
                         mkCons
                           {pair data data}
                           (mkPairData
                              (case data hd [(\(l : data) (r : data) -> l)])
                              (`$dToData`
                                 (f
                                    (`$dUnsafeFromData`
                                       (case
                                          data
                                          hd
                                          [(\(l : data) (r : data) -> r)])))))
                           (go eta))
                    , [] ]
          in
          go
in
letrec
  !safeAppend :
     list (pair data data) -> list (pair data data) -> list (pair data data)
    = \(xs : list (pair data data)) (xs : list (pair data data)) ->
        case
          (list (pair data data))
          xs
          [ (\(hd : pair data data) (tl : list (pair data data)) ->
               let
                 !v : data = case data hd [(\(l : data) (r : data) -> r)]
                 !k : data = case data hd [(\(l : data) (r : data) -> l)]
                 !eta : list (pair data data) = safeAppend tl xs
                 !nilCase : list (pair data data)
                   = mkCons {pair data data} (mkPairData k v) []
               in
               letrec
                 !go : list (pair data data) -> list (pair data data)
                   = \(xs : list (pair data data)) ->
                       case
                         (list (pair data data))
                         xs
                         [ (\(hd : pair data data) ->
                              case
                                (all dead.
                                   list (pair data data) ->
                                   list (pair data data))
                                (equalsData
                                   k
                                   (case
                                      data
                                      hd
                                      [(\(l : data) (r : data) -> l)]))
                                [ (/\dead ->
                                     \(eta : list (pair data data)) ->
                                       mkCons {pair data data} hd (go eta))
                                , (/\dead ->
                                     mkCons {pair data data} (mkPairData k v)) ]
                                {all dead. dead})
                         , nilCase ]
               in
               go eta)
          , xs ]
in
let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !lookup' : data -> list (pair data data) -> Maybe data
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
        \(m : list (pair data data)) -> go m
  !union :
     all k a b.
       (\a -> data -> a) a ->
       (\a -> data -> a) b ->
       (\a -> a -> data) a ->
       (\a -> a -> data) b ->
       (\k a -> list (pair data data)) k a ->
       (\k a -> list (pair data data)) k b ->
       (\k a -> list (pair data data)) k (These a b)
    = /\k a b ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a)
         (`$dUnsafeFromData` : (\a -> data -> a) b)
         (`$dToData` : (\a -> a -> data) a)
         (`$dToData` : (\a -> a -> data) b)
         (ds : (\k a -> list (pair data data)) k a) ->
          letrec
            !goRight : list (pair data data) -> list (pair data data)
              = \(xs : list (pair data data)) ->
                  case
                    (list (pair data data))
                    xs
                    [ (\(hd : pair data data) (tl : list (pair data data)) ->
                         let
                           !v : data
                             = case data hd [(\(l : data) (r : data) -> r)]
                           !k : data
                             = case data hd [(\(l : data) (r : data) -> l)]
                         in
                         Maybe_match
                           {data}
                           (lookup' k ds)
                           {all dead. list (pair data data)}
                           (\(r : data) ->
                              /\dead ->
                                mkCons
                                  {pair data data}
                                  (mkPairData
                                     k
                                     (`$fToDataThese_$ctoBuiltinData`
                                        {a}
                                        {b}
                                        `$dToData`
                                        `$dToData`
                                        (These
                                           {a}
                                           {b}
                                           (`$dUnsafeFromData` v)
                                           (`$dUnsafeFromData` r))))
                                  (goRight tl))
                           (/\dead ->
                              mkCons
                                {pair data data}
                                (mkPairData
                                   k
                                   (`$fToDataThese_$ctoBuiltinData`
                                      {a}
                                      {b}
                                      `$dToData`
                                      `$dToData`
                                      (That {a} {b} (`$dUnsafeFromData` v))))
                                (goRight tl))
                           {all dead. dead})
                    , [] ]
          in
          \(ds : (\k a -> list (pair data data)) k b) ->
            letrec
              !goLeft : list (pair data data) -> list (pair data data)
                = \(xs : list (pair data data)) ->
                    case
                      (list (pair data data))
                      xs
                      [ (\(hd : pair data data) (tl : list (pair data data)) ->
                           let
                             !v : data
                               = case data hd [(\(l : data) (r : data) -> r)]
                             !k : data
                               = case data hd [(\(l : data) (r : data) -> l)]
                           in
                           Maybe_match
                             {data}
                             (lookup' k ds)
                             {all dead. list (pair data data)}
                             (\(r : data) ->
                                /\dead ->
                                  mkCons
                                    {pair data data}
                                    (mkPairData
                                       k
                                       (`$fToDataThese_$ctoBuiltinData`
                                          {a}
                                          {b}
                                          `$dToData`
                                          `$dToData`
                                          (These
                                             {a}
                                             {b}
                                             (`$dUnsafeFromData` v)
                                             (`$dUnsafeFromData` r))))
                                    (goLeft tl))
                             (/\dead ->
                                mkCons
                                  {pair data data}
                                  (mkPairData
                                     k
                                     (`$fToDataThese_$ctoBuiltinData`
                                        {a}
                                        {b}
                                        `$dToData`
                                        `$dToData`
                                        (This {a} {b} (`$dUnsafeFromData` v))))
                                  (goLeft tl))
                             {all dead. dead})
                      , [] ]
            in
            safeAppend (goLeft ds) (goRight ds)
in
\(bd : data) (bd : data) ->
  let
    !value :
       (\k a -> list (pair data data))
         bytestring
         ((\k a -> list (pair data data)) bytestring integer)
      = let
        !ls :
           (\k a -> list (pair data data))
             bytestring
             ((\k a -> list (pair data data)) bytestring integer)
          = unMapData bd
        !rs :
           (\k a -> list (pair data data))
             bytestring
             ((\k a -> list (pair data data)) bytestring integer)
          = unMapData bd
      in
      map
        {bytestring}
        {(\k a -> list (pair data data)) bytestring (These integer integer)}
        {(\k a -> list (pair data data)) bytestring integer}
        (\(eta : data) -> unMapData eta)
        (`$fToDataMap_$ctoBuiltinData` {bytestring} {integer})
        (map
           {bytestring}
           {These integer integer}
           {integer}
           (`$fUnsafeFromDataThese_$cunsafeFromBuiltinData`
              {integer}
              {integer}
              unIData
              unIData)
           `$fToDataInteger_$ctoBuiltinData`
           (\(k' : These integer integer) ->
              These_match
                {integer}
                {integer}
                k'
                {integer}
                (\(b : integer) -> addInteger 0 b)
                (\(a : integer) (b : integer) -> addInteger a b)
                (\(a : integer) -> addInteger 0 a)))
        (map
           {bytestring}
           {These
              ((\k a -> list (pair data data)) bytestring integer)
              ((\k a -> list (pair data data)) bytestring integer)}
           {(\k a -> list (pair data data)) bytestring (These integer integer)}
           (`$fUnsafeFromDataThese_$cunsafeFromBuiltinData`
              {(\k a -> list (pair data data)) bytestring integer}
              {(\k a -> list (pair data data)) bytestring integer}
              (\(eta : data) -> unMapData eta)
              (\(eta : data) -> unMapData eta))
           (`$fToDataMap_$ctoBuiltinData` {bytestring} {These integer integer})
           (\(k :
                These
                  ((\k a -> list (pair data data)) bytestring integer)
                  ((\k a -> list (pair data data)) bytestring integer)) ->
              These_match
                {(\k a -> list (pair data data)) bytestring integer}
                {(\k a -> list (pair data data)) bytestring integer}
                k
                {(\k a -> list (pair data data))
                   bytestring
                   (These integer integer)}
                (\(b : (\k a -> list (pair data data)) bytestring integer) ->
                   map
                     {bytestring}
                     {integer}
                     {These integer integer}
                     unIData
                     `$dToData`
                     (\(ds : integer) -> That {integer} {integer} ds)
                     b)
                (\(a : (\k a -> list (pair data data)) bytestring integer)
                  (b : (\k a -> list (pair data data)) bytestring integer) ->
                   union
                     {bytestring}
                     {integer}
                     {integer}
                     unIData
                     unIData
                     `$fToDataInteger_$ctoBuiltinData`
                     `$fToDataInteger_$ctoBuiltinData`
                     a
                     b)
                (\(a : (\k a -> list (pair data data)) bytestring integer) ->
                   map
                     {bytestring}
                     {integer}
                     {These integer integer}
                     unIData
                     `$dToData`
                     (\(ds : integer) -> This {integer} {integer} ds)
                     a))
           (union
              {bytestring}
              {(\k a -> list (pair data data)) bytestring integer}
              {(\k a -> list (pair data data)) bytestring integer}
              (\(eta : data) -> unMapData eta)
              (\(eta : data) -> unMapData eta)
              (`$fToDataMap_$ctoBuiltinData` {bytestring} {integer})
              (`$fToDataMap_$ctoBuiltinData` {bytestring} {integer})
              ls
              rs))
  in
  Maybe_match
    {data}
    (lookup' (B #) value)
    {integer}
    (\(a : data) ->
       let
         !m : list (pair data data) = unMapData a
       in
       Maybe_match
         {data}
         (lookup' (B #) m)
         {integer}
         (\(a : data) -> unIData a)
         0)
    0
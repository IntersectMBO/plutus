let
  !`$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData` : data -> data
    = \(d : data) -> d
  !filter :
     all a.
       (\a -> data -> a) a ->
       (\a -> a -> data) a ->
       (a -> bool) ->
       (\a -> list data) a ->
       (\a -> list data) a
    = /\a ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a)
         (`$dToData` : (\a -> a -> data) a)
         (pred : a -> bool) ->
          letrec
            !go : (\a -> list data) a -> (\a -> list data) a
              = \(ds : (\a -> list data) a) ->
                  case
                    ((\a -> list data) a)
                    ds
                    [ (\(x : data) (eta : list data) ->
                         let
                           !h : a = `$dUnsafeFromData` x
                         in
                         case
                           (all dead. (\a -> list data) a)
                           (pred h)
                           [ (/\dead -> go eta)
                           , (/\dead ->
                                let
                                  !nt : list data = go eta
                                in
                                mkCons {data} (`$dToData` h) nt) ]
                           {all dead. dead})
                    , [] ]
          in
          \(eta : (\a -> list data) a) -> go eta
  !member :
     all k a.
       (\a -> a -> data) k -> k -> (\k a -> list (pair data data)) k a -> bool
    = /\k a ->
        \(`$dToData` : (\a -> a -> data) k) (ds : k) ->
          letrec
            !go : list (pair data data) -> bool
              = \(xs : list (pair data data)) ->
                  case
                    bool
                    xs
                    [ (\(hd : pair data data) ->
                         case
                           (all dead. list (pair data data) -> bool)
                           (equalsData
                              (`$dToData` ds)
                              (case data hd [(\(l : data) (r : data) -> l)]))
                           [ (/\dead -> go)
                           , (/\dead -> \(ds : list (pair data data)) -> True) ]
                           {all dead. dead})
                    , False ]
          in
          \(ds : (\k a -> list (pair data data)) k a) -> go ds
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !mapMaybe :
     all k a b.
       (\a -> data -> a) a ->
       (\a -> a -> data) b ->
       (a -> Maybe b) ->
       (\k a -> list (pair data data)) k a ->
       (\k a -> list (pair data data)) k b
    = /\k a b ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a)
         (`$dToData` : (\a -> a -> data) b)
         (f : a -> Maybe b) ->
          letrec
            !go : list (pair data data) -> list (pair data data)
              = \(xs : list (pair data data)) ->
                  case
                    (list (pair data data))
                    xs
                    [ (\(hd : pair data data) ->
                         Maybe_match
                           {b}
                           (f
                              (`$dUnsafeFromData`
                                 (case
                                    data
                                    hd
                                    [(\(l : data) (r : data) -> r)])))
                           {all dead.
                              list (pair data data) -> list (pair data data)}
                           (\(v' : b) ->
                              /\dead ->
                                \(eta : list (pair data data)) ->
                                  mkCons
                                    {pair data data}
                                    (mkPairData
                                       (case
                                          data
                                          hd
                                          [(\(l : data) (r : data) -> l)])
                                       (`$dToData` v'))
                                    (go eta))
                           (/\dead -> go)
                           {all dead. dead})
                    , [] ]
          in
          go
  !null : all a. (\a -> list data) a -> bool
    = /\a -> \(eta : (\a -> list data) a) -> nullList {data} eta
  data Unit | Unit_match where
    Unit : Unit
in
\(ds : data) ->
  let
    !l : list data
      = case
          (list data)
          (unConstrData ds)
          [(\(l : integer) (r : list data) -> r)]
    !scriptInfo : data = headList {data} (tailList {data} (tailList {data} l))
    !l : list data
      = case
          (list data)
          (unConstrData (headList {data} l))
          [(\(l : integer) (r : list data) -> r)]
    !l : list data
      = tailList {data} (tailList {data} (tailList {data} (tailList {data} l)))
    !l : list data = tailList {data} l
    !l : list data = tailList {data} l
  in
  case
    (all dead. unit)
    (let
      !tup : pair integer (list data) = unConstrData scriptInfo
    in
    case
      (all dead. bool)
      (equalsInteger
         0
         (case integer tup [(\(l : integer) (r : list data) -> l)]))
      [ (/\dead ->
           let
             !tup : pair integer (list data) = unConstrData scriptInfo
           in
           case
             (all dead. bool)
             (equalsInteger
                1
                (case integer tup [(\(l : integer) (r : list data) -> l)]))
             [ (/\dead ->
                  let
                    !tup : pair integer (list data) = unConstrData scriptInfo
                  in
                  case
                    (all dead. bool)
                    (equalsInteger
                       2
                       (case
                          integer
                          tup
                          [(\(l : integer) (r : list data) -> l)]))
                    [ (/\dead ->
                         let
                           !tup : pair integer (list data)
                             = unConstrData scriptInfo
                         in
                         case
                           (all dead. bool)
                           (equalsInteger
                              3
                              (case
                                 integer
                                 tup
                                 [(\(l : integer) (r : list data) -> l)]))
                           [ (/\dead ->
                                let
                                  !tup : pair integer (list data)
                                    = unConstrData scriptInfo
                                in
                                case
                                  (all dead. bool)
                                  (equalsInteger
                                     4
                                     (case
                                        integer
                                        tup
                                        [ (\(l : integer) (r : list data) ->
                                             l) ]))
                                  [ (/\dead ->
                                       let
                                         !tup : pair integer (list data)
                                           = unConstrData scriptInfo
                                       in
                                       case
                                         (all dead. bool)
                                         (equalsInteger
                                            5
                                            (case
                                               integer
                                               tup
                                               [ (\(l : integer)
                                                   (r : list data) ->
                                                    l) ]))
                                         [ (/\dead ->
                                              let
                                                !defaultBody : bool
                                                  = error {bool}
                                              in
                                              Unit_match
                                                (error {Unit})
                                                {bool}
                                                defaultBody)
                                         , (/\dead ->
                                              let
                                                !l : list data
                                                  = case
                                                      (list data)
                                                      tup
                                                      [ (\(l : integer)
                                                          (r : list data) ->
                                                           r) ]
                                              in
                                              True) ]
                                         {all dead. dead})
                                  , (/\dead ->
                                       member
                                         {data}
                                         {(\k a -> list (pair data data))
                                            data
                                            data}
                                         (\(x : data) -> x)
                                         (headList
                                            {data}
                                            (case
                                               (list data)
                                               tup
                                               [ (\(l : integer)
                                                   (r : list data) ->
                                                    r) ]))
                                         (unMapData
                                            (headList
                                               {data}
                                               (tailList
                                                  {data}
                                                  (tailList
                                                     {data}
                                                     (tailList
                                                        {data}
                                                        (tailList
                                                           {data}
                                                           (tailList
                                                              {data}
                                                              (tailList
                                                                 {data}
                                                                 l))))))))) ]
                                  {all dead. dead})
                           , (/\dead ->
                                let
                                  !l : list data
                                    = case
                                        (list data)
                                        tup
                                        [(\(l : integer) (r : list data) -> r)]
                                in
                                (let
                                    a = (\a -> list data) data
                                  in
                                  /\b -> \(f : a -> b) (x : a) -> f x)
                                  {bool}
                                  (null {data})
                                  (filter
                                     {data}
                                     `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                     (\(x : data) -> x)
                                     (\(v : data) ->
                                        equalsData
                                          (headList {data} (tailList {data} l))
                                          v)
                                     (unListData (headList {data} l)))) ]
                           {all dead. dead})
                    , (/\dead ->
                         member
                           {data}
                           {integer}
                           (\(x : data) -> x)
                           (headList
                              {data}
                              (case
                                 (list data)
                                 tup
                                 [(\(l : integer) (r : list data) -> r)]))
                           (unMapData (headList {data} l))) ]
                    {all dead. dead})
             , (/\dead ->
                  let
                    !l : list data
                      = case
                          (list data)
                          tup
                          [(\(l : integer) (r : list data) -> r)]
                  in
                  Maybe_match
                    {data}
                    ((let
                         b = list data
                       in
                       /\r ->
                         \(p : pair integer b) (f : integer -> b -> r) ->
                           case r p [f])
                       {Maybe data}
                       (unConstrData (headList {data} (tailList {data} l)))
                       (\(index : integer) (args : list data) ->
                          case
                            (list data -> Maybe data)
                            index
                            [ (\(ds : list data) ->
                                 Just {data} (headList {data} ds))
                            , (\(ds : list data) -> Nothing {data}) ]
                            args))
                    {all dead. bool}
                    (\(ds : data) -> /\dead -> False)
                    (/\dead ->
                       (let
                           a = (\a -> list data) data
                         in
                         /\b -> \(f : a -> b) (x : a) -> f x)
                         {bool}
                         (null {data})
                         (filter
                            {data}
                            `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                            (\(x : data) -> x)
                            (\(x : data) ->
                               equalsData
                                 (headList {data} l)
                                 (headList
                                    {data}
                                    (case
                                       (list data)
                                       (unConstrData x)
                                       [ (\(l : integer) (r : list data) ->
                                            r) ])))
                            (unListData (headList {data} l))))
                    {all dead. dead}) ]
             {all dead. dead})
      , (/\dead ->
           (let
               a
                 = (\k a -> list (pair data data))
                     bytestring
                     ((\k a -> list (pair data data)) bytestring integer)
             in
             /\b -> \(f : a -> b) (x : a) -> f x)
             {bool}
             ((let
                  b
                    = (\k a -> list (pair data data))
                        bytestring
                        ((\k a -> list (pair data data)) bytestring integer)
                in
                /\c a -> \(f : b -> c) (g : a -> b) (x : a) -> f (g x))
                {bool}
                {(\k a -> list (pair data data))
                   bytestring
                   ((\k a -> list (pair data data)) bytestring integer)}
                (member
                   {bytestring}
                   {(\k a -> list (pair data data)) bytestring integer}
                   bData
                   (unBData
                      (headList
                         {data}
                         (case
                            (list data)
                            tup
                            [(\(l : integer) (r : list data) -> r)]))))
                (\(ds :
                     (\k a -> list (pair data data))
                       bytestring
                       ((\k a -> list (pair data data)) bytestring integer)) ->
                   ds))
             (mapMaybe
                {bytestring}
                {(\k a -> list (pair data data)) bytestring integer}
                {(\k a -> list (pair data data)) bytestring integer}
                (\(eta : data) -> unMapData eta)
                (\(ds : (\k a -> list (pair data data)) bytestring integer) ->
                   mapData ds)
                (\(map : (\k a -> list (pair data data)) bytestring integer) ->
                   let
                     !l : list (pair data data)
                       = mapMaybe
                           {bytestring}
                           {integer}
                           {integer}
                           unIData
                           (\(i : integer) -> iData i)
                           (\(x : integer) ->
                              case
                                (all dead. Maybe integer)
                                (case
                                   bool
                                   (lessThanEqualsInteger x 0)
                                   [True, False])
                                [ (/\dead -> Nothing {integer})
                                , (/\dead -> Just {integer} x) ]
                                {all dead. dead})
                           map
                   in
                   case
                     (all dead.
                        Maybe
                          ((\k a -> list (pair data data)) bytestring integer))
                     (nullList {pair data data} l)
                     [ (/\dead ->
                          Just
                            {(\k a -> list (pair data data)) bytestring integer}
                            l)
                     , (/\dead ->
                          Nothing
                            {(\k a -> list (pair data data))
                               bytestring
                               integer}) ]
                     {all dead. dead})
                (unMapData (headList {data} l)))) ]
      {all dead. dead})
    [ (/\dead -> let !x : Unit = trace {Unit} "PT5" Unit in error {unit})
    , (/\dead -> ()) ]
    {all dead. dead}
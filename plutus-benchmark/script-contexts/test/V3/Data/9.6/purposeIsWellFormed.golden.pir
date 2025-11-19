let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !`$dEq` : Maybe integer -> Maybe integer -> bool
    = \(ds : Maybe integer) (ds : Maybe integer) ->
        Maybe_match
          {integer}
          ds
          {all dead. bool}
          (\(l1l : integer) ->
             /\dead ->
               Maybe_match
                 {integer}
                 ds
                 {bool}
                 (\(r1r : integer) -> equalsInteger l1l r1r)
                 False)
          (/\dead ->
             Maybe_match {integer} ds {bool} (\(ipv : integer) -> False) True)
          {all dead. dead}
  !`$fEqCredential_$c==` : data -> data -> bool
    = \(ds : data) (ds : data) ->
        let
          !fail : unit -> bool
            = \(ds : unit) ->
                let
                  !tup : pair integer (list data) = unConstrData ds
                in
                case
                  (all dead. bool)
                  (equalsInteger
                     1
                     (case integer tup [(\(l : integer) (r : list data) -> l)]))
                  [ (/\dead -> False)
                  , (/\dead ->
                       let
                         !tup : pair integer (list data) = unConstrData ds
                       in
                       case
                         (all dead. bool)
                         (equalsInteger
                            1
                            (case
                               integer
                               tup
                               [(\(l : integer) (r : list data) -> l)]))
                         [ (/\dead -> False)
                         , (/\dead ->
                              equalsByteString
                                (unBData
                                   (headList
                                      {data}
                                      (case
                                         (list data)
                                         tup
                                         [ (\(l : integer) (r : list data) ->
                                              r) ])))
                                (unBData
                                   (headList
                                      {data}
                                      (case
                                         (list data)
                                         tup
                                         [ (\(l : integer) (r : list data) ->
                                              r) ])))) ]
                         {all dead. dead}) ]
                  {all dead. dead}
          !tup : pair integer (list data) = unConstrData ds
        in
        case
          (all dead. bool)
          (equalsInteger
             0
             (case integer tup [(\(l : integer) (r : list data) -> l)]))
          [ (/\dead -> fail ())
          , (/\dead ->
               let
                 !tup : pair integer (list data) = unConstrData ds
               in
               case
                 (all dead. bool)
                 (equalsInteger
                    0
                    (case integer tup [(\(l : integer) (r : list data) -> l)]))
                 [ (/\dead -> fail ())
                 , (/\dead ->
                      equalsByteString
                        (unBData
                           (headList
                              {data}
                              (case
                                 (list data)
                                 tup
                                 [(\(l : integer) (r : list data) -> r)])))
                        (unBData
                           (headList
                              {data}
                              (case
                                 (list data)
                                 tup
                                 [(\(l : integer) (r : list data) -> r)])))) ]
                 {all dead. dead}) ]
          {all dead. dead}
  !`$fEqDRep0_$c==` : data -> data -> bool
    = \(ds : data) (ds : data) ->
        let
          !fail : unit -> bool
            = \(ds : unit) ->
                case
                  (all dead. bool)
                  (equalsInteger
                     2
                     (case
                        integer
                        (unConstrData ds)
                        [(\(l : integer) (r : list data) -> l)]))
                  [ (/\dead -> False)
                  , (/\dead ->
                       equalsInteger
                         2
                         (case
                            integer
                            (unConstrData ds)
                            [(\(l : integer) (r : list data) -> l)])) ]
                  {all dead. dead}
          !fail : unit -> bool
            = \(ds : unit) ->
                case
                  (all dead. bool)
                  (equalsInteger
                     1
                     (case
                        integer
                        (unConstrData ds)
                        [(\(l : integer) (r : list data) -> l)]))
                  [ (/\dead -> fail ())
                  , (/\dead ->
                       case
                         (all dead. bool)
                         (equalsInteger
                            1
                            (case
                               integer
                               (unConstrData ds)
                               [(\(l : integer) (r : list data) -> l)]))
                         [(/\dead -> fail ()), (/\dead -> True)]
                         {all dead. dead}) ]
                  {all dead. dead}
          !tup : pair integer (list data) = unConstrData ds
        in
        case
          (all dead. bool)
          (equalsInteger
             0
             (case integer tup [(\(l : integer) (r : list data) -> l)]))
          [ (/\dead -> fail ())
          , (/\dead ->
               let
                 !tup : pair integer (list data) = unConstrData ds
               in
               case
                 (all dead. bool)
                 (equalsInteger
                    0
                    (case integer tup [(\(l : integer) (r : list data) -> l)]))
                 [ (/\dead -> fail ())
                 , (/\dead ->
                      `$fEqCredential_$c==`
                        (headList
                           {data}
                           (case
                              (list data)
                              tup
                              [(\(l : integer) (r : list data) -> r)]))
                        (headList
                           {data}
                           (case
                              (list data)
                              tup
                              [(\(l : integer) (r : list data) -> r)]))) ]
                 {all dead. dead}) ]
          {all dead. dead}
  !`$mDelegStakeVote` :
     all r. data -> (bytestring -> data -> r) -> (unit -> r) -> r
    = /\r ->
        \(scrut : data) (cont : bytestring -> data -> r) (fail : unit -> r) ->
          let
            !tup : pair integer (list data) = unConstrData scrut
          in
          case
            (all dead. r)
            (equalsInteger
               2
               (case integer tup [(\(l : integer) (r : list data) -> l)]))
            [ (/\dead -> fail ())
            , (/\dead ->
                 let
                   !l : list data
                     = case
                         (list data)
                         tup
                         [(\(l : integer) (r : list data) -> r)]
                 in
                 cont
                   (unBData (headList {data} l))
                   (headList {data} (tailList {data} l))) ]
            {all dead. dead}
  !`$fEqDelegatee0_$c==` : data -> data -> bool
    = \(ds : data) (ds : data) ->
        let
          !fail : unit -> bool
            = \(ds : unit) ->
                `$mDelegStakeVote`
                  {bool}
                  ds
                  (\(a : bytestring) (b : data) ->
                     `$mDelegStakeVote`
                       {bool}
                       ds
                       (\(a' : bytestring) (b' : data) ->
                          case
                            (all dead. bool)
                            (equalsByteString a a')
                            [ (/\dead -> False)
                            , (/\dead -> `$fEqDRep0_$c==` b b') ]
                            {all dead. dead})
                       (\(void : unit) -> False))
                  (\(void : unit) -> False)
          !fail : unit -> bool
            = \(ds : unit) ->
                let
                  !tup : pair integer (list data) = unConstrData ds
                in
                case
                  (all dead. bool)
                  (equalsInteger
                     1
                     (case integer tup [(\(l : integer) (r : list data) -> l)]))
                  [ (/\dead -> fail ())
                  , (/\dead ->
                       let
                         !tup : pair integer (list data) = unConstrData ds
                       in
                       case
                         (all dead. bool)
                         (equalsInteger
                            1
                            (case
                               integer
                               tup
                               [(\(l : integer) (r : list data) -> l)]))
                         [ (/\dead -> fail ())
                         , (/\dead ->
                              `$fEqDRep0_$c==`
                                (headList
                                   {data}
                                   (case
                                      (list data)
                                      tup
                                      [(\(l : integer) (r : list data) -> r)]))
                                (headList
                                   {data}
                                   (case
                                      (list data)
                                      tup
                                      [ (\(l : integer) (r : list data) ->
                                           r) ]))) ]
                         {all dead. dead}) ]
                  {all dead. dead}
          !tup : pair integer (list data) = unConstrData ds
        in
        case
          (all dead. bool)
          (equalsInteger
             0
             (case integer tup [(\(l : integer) (r : list data) -> l)]))
          [ (/\dead -> fail ())
          , (/\dead ->
               let
                 !tup : pair integer (list data) = unConstrData ds
               in
               case
                 (all dead. bool)
                 (equalsInteger
                    0
                    (case integer tup [(\(l : integer) (r : list data) -> l)]))
                 [ (/\dead -> fail ())
                 , (/\dead ->
                      equalsByteString
                        (unBData
                           (headList
                              {data}
                              (case
                                 (list data)
                                 tup
                                 [(\(l : integer) (r : list data) -> r)])))
                        (unBData
                           (headList
                              {data}
                              (case
                                 (list data)
                                 tup
                                 [(\(l : integer) (r : list data) -> r)])))) ]
                 {all dead. dead}) ]
          {all dead. dead}
  !`$mTxCertRegDRep` : all r. data -> (data -> integer -> r) -> (unit -> r) -> r
    = /\r ->
        \(scrut : data) (cont : data -> integer -> r) (fail : unit -> r) ->
          let
            !tup : pair integer (list data) = unConstrData scrut
          in
          case
            (all dead. r)
            (equalsInteger
               4
               (case integer tup [(\(l : integer) (r : list data) -> l)]))
            [ (/\dead -> fail ())
            , (/\dead ->
                 let
                   !l : list data
                     = case
                         (list data)
                         tup
                         [(\(l : integer) (r : list data) -> r)]
                 in
                 cont
                   (headList {data} l)
                   (unIData (headList {data} (tailList {data} l)))) ]
            {all dead. dead}
  !`$mTxCertRegDeleg` :
     all r. data -> (data -> data -> integer -> r) -> (unit -> r) -> r
    = /\r ->
        \(scrut : data)
         (cont : data -> data -> integer -> r)
         (fail : unit -> r) ->
          let
            !tup : pair integer (list data) = unConstrData scrut
          in
          case
            (all dead. r)
            (equalsInteger
               3
               (case integer tup [(\(l : integer) (r : list data) -> l)]))
            [ (/\dead -> fail ())
            , (/\dead ->
                 let
                   !l : list data
                     = case
                         (list data)
                         tup
                         [(\(l : integer) (r : list data) -> r)]
                   !l : list data = tailList {data} l
                 in
                 cont
                   (headList {data} l)
                   (headList {data} l)
                   (unIData (headList {data} (tailList {data} l)))) ]
            {all dead. dead}
  !`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData` :
     all a. (\a -> data -> a) a -> data -> Maybe a
    = /\a ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
          (let
              b = list data
            in
            /\r ->
              \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
            {Maybe a}
            (unConstrData d)
            (\(index : integer) (args : list data) ->
               case
                 (list data -> Maybe a)
                 index
                 [ (\(ds : list data) ->
                      Just {a} (`$dUnsafeFromData` (headList {data} ds)))
                 , (\(ds : list data) -> Nothing {a}) ]
                 args)
  !`$mTxCertRegStaking` :
     all r. data -> (data -> Maybe integer -> r) -> (unit -> r) -> r
    = /\r ->
        \(scrut : data)
         (cont : data -> Maybe integer -> r)
         (fail : unit -> r) ->
          let
            !tup : pair integer (list data) = unConstrData scrut
          in
          case
            (all dead. r)
            (equalsInteger
               0
               (case integer tup [(\(l : integer) (r : list data) -> l)]))
            [ (/\dead -> fail ())
            , (/\dead ->
                 let
                   !l : list data
                     = case
                         (list data)
                         tup
                         [(\(l : integer) (r : list data) -> r)]
                 in
                 cont
                   (headList {data} l)
                   (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                      {integer}
                      unIData
                      (headList {data} (tailList {data} l)))) ]
            {all dead. dead}
  !`$mTxCertUnRegDRep` :
     all r. data -> (data -> integer -> r) -> (unit -> r) -> r
    = /\r ->
        \(scrut : data) (cont : data -> integer -> r) (fail : unit -> r) ->
          let
            !tup : pair integer (list data) = unConstrData scrut
          in
          case
            (all dead. r)
            (equalsInteger
               6
               (case integer tup [(\(l : integer) (r : list data) -> l)]))
            [ (/\dead -> fail ())
            , (/\dead ->
                 let
                   !l : list data
                     = case
                         (list data)
                         tup
                         [(\(l : integer) (r : list data) -> r)]
                 in
                 cont
                   (headList {data} l)
                   (unIData (headList {data} (tailList {data} l)))) ]
            {all dead. dead}
  !`$mTxCertUnRegStaking` :
     all r. data -> (data -> Maybe integer -> r) -> (unit -> r) -> r
    = /\r ->
        \(scrut : data)
         (cont : data -> Maybe integer -> r)
         (fail : unit -> r) ->
          let
            !tup : pair integer (list data) = unConstrData scrut
          in
          case
            (all dead. r)
            (equalsInteger
               1
               (case integer tup [(\(l : integer) (r : list data) -> l)]))
            [ (/\dead -> fail ())
            , (/\dead ->
                 let
                   !l : list data
                     = case
                         (list data)
                         tup
                         [(\(l : integer) (r : list data) -> r)]
                 in
                 cont
                   (headList {data} l)
                   (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                      {integer}
                      unIData
                      (headList {data} (tailList {data} l)))) ]
            {all dead. dead}
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
  !txOutRefId : data -> bytestring
    = \(ds : data) ->
        unBData
          (headList
             {data}
             (case
                (list data)
                (unConstrData ds)
                [(\(l : integer) (r : list data) -> r)]))
  !txOutRefIdx : data -> integer
    = \(ds : data) ->
        unIData
          (headList
             {data}
             (tailList
                {data}
                (case
                   (list data)
                   (unConstrData ds)
                   [(\(l : integer) (r : list data) -> r)])))
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
                                        let
                                          !eta : data
                                            = headList
                                                {data}
                                                (tailList {data} l)
                                          !fail :
                                             unit -> bool
                                            = \(ds : unit) ->
                                                let
                                                  !tup :
                                                     pair integer (list data)
                                                    = unConstrData eta
                                                in
                                                case
                                                  (all dead. bool)
                                                  (equalsInteger
                                                     10
                                                     (case
                                                        integer
                                                        tup
                                                        [ (\(l : integer)
                                                            (r : list data) ->
                                                             l) ]))
                                                  [ (/\dead -> False)
                                                  , (/\dead ->
                                                       let
                                                         !tup :
                                                            pair
                                                              integer
                                                              (list data)
                                                           = unConstrData v
                                                       in
                                                       case
                                                         (all dead. bool)
                                                         (equalsInteger
                                                            10
                                                            (case
                                                               integer
                                                               tup
                                                               [ (\(l : integer)
                                                                   (r :
                                                                      list
                                                                        data) ->
                                                                    l) ]))
                                                         [ (/\dead -> False)
                                                         , (/\dead ->
                                                              `$fEqCredential_$c==`
                                                                (headList
                                                                   {data}
                                                                   (case
                                                                      (list
                                                                         data)
                                                                      tup
                                                                      [ (\(l :
                                                                             integer)
                                                                          (r :
                                                                             list
                                                                               data) ->
                                                                           r) ]))
                                                                (headList
                                                                   {data}
                                                                   (case
                                                                      (list
                                                                         data)
                                                                      tup
                                                                      [ (\(l :
                                                                             integer)
                                                                          (r :
                                                                             list
                                                                               data) ->
                                                                           r) ]))) ]
                                                         {all dead. dead}) ]
                                                  {all dead. dead}
                                          !fail :
                                             unit -> bool
                                            = \(ds : unit) ->
                                                let
                                                  !tup :
                                                     pair integer (list data)
                                                    = unConstrData eta
                                                in
                                                case
                                                  (all dead. bool)
                                                  (equalsInteger
                                                     9
                                                     (case
                                                        integer
                                                        tup
                                                        [ (\(l : integer)
                                                            (r : list data) ->
                                                             l) ]))
                                                  [ (/\dead -> fail ())
                                                  , (/\dead ->
                                                       let
                                                         !l : list data
                                                           = case
                                                               (list data)
                                                               tup
                                                               [ (\(l : integer)
                                                                   (r :
                                                                      list
                                                                        data) ->
                                                                    r) ]
                                                         !tup :
                                                            pair
                                                              integer
                                                              (list data)
                                                           = unConstrData v
                                                       in
                                                       case
                                                         (all dead. bool)
                                                         (equalsInteger
                                                            9
                                                            (case
                                                               integer
                                                               tup
                                                               [ (\(l : integer)
                                                                   (r :
                                                                      list
                                                                        data) ->
                                                                    l) ]))
                                                         [ (/\dead -> fail ())
                                                         , (/\dead ->
                                                              let
                                                                !l :
                                                                   list data
                                                                  = case
                                                                      (list
                                                                         data)
                                                                      tup
                                                                      [ (\(l :
                                                                             integer)
                                                                          (r :
                                                                             list
                                                                               data) ->
                                                                           r) ]
                                                              in
                                                              case
                                                                (all dead. bool)
                                                                (`$fEqCredential_$c==`
                                                                   (headList
                                                                      {data}
                                                                      l)
                                                                   (headList
                                                                      {data}
                                                                      l))
                                                                [ (/\dead ->
                                                                     False)
                                                                , (/\dead ->
                                                                     `$fEqCredential_$c==`
                                                                       (headList
                                                                          {data}
                                                                          (tailList
                                                                             {data}
                                                                             l))
                                                                       (headList
                                                                          {data}
                                                                          (tailList
                                                                             {data}
                                                                             l))) ]
                                                                {all dead.
                                                                   dead}) ]
                                                         {all dead. dead}) ]
                                                  {all dead. dead}
                                          !fail :
                                             unit -> bool
                                            = \(ds : unit) ->
                                                `$mTxCertUnRegDRep`
                                                  {bool}
                                                  eta
                                                  (\(a : data)
                                                    (b : integer) ->
                                                     `$mTxCertUnRegDRep`
                                                       {bool}
                                                       v
                                                       (\(a' : data)
                                                         (b' : integer) ->
                                                          case
                                                            (all dead. bool)
                                                            (`$fEqCredential_$c==`
                                                               a
                                                               a')
                                                            [ (/\dead -> False)
                                                            , (/\dead ->
                                                                 equalsInteger
                                                                   b
                                                                   b') ]
                                                            {all dead. dead})
                                                       (\(void : unit) ->
                                                          fail ()))
                                                  (\(void : unit) -> fail ())
                                          !fail :
                                             unit -> bool
                                            = \(ds : unit) ->
                                                let
                                                  !tup :
                                                     pair integer (list data)
                                                    = unConstrData eta
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
                                                  [ (/\dead -> fail ())
                                                  , (/\dead ->
                                                       let
                                                         !tup :
                                                            pair
                                                              integer
                                                              (list data)
                                                           = unConstrData v
                                                       in
                                                       case
                                                         (all dead. bool)
                                                         (equalsInteger
                                                            5
                                                            (case
                                                               integer
                                                               tup
                                                               [ (\(l : integer)
                                                                   (r :
                                                                      list
                                                                        data) ->
                                                                    l) ]))
                                                         [ (/\dead -> fail ())
                                                         , (/\dead ->
                                                              `$fEqCredential_$c==`
                                                                (headList
                                                                   {data}
                                                                   (case
                                                                      (list
                                                                         data)
                                                                      tup
                                                                      [ (\(l :
                                                                             integer)
                                                                          (r :
                                                                             list
                                                                               data) ->
                                                                           r) ]))
                                                                (headList
                                                                   {data}
                                                                   (case
                                                                      (list
                                                                         data)
                                                                      tup
                                                                      [ (\(l :
                                                                             integer)
                                                                          (r :
                                                                             list
                                                                               data) ->
                                                                           r) ]))) ]
                                                         {all dead. dead}) ]
                                                  {all dead. dead}
                                          !fail :
                                             unit -> bool
                                            = \(ds : unit) ->
                                                `$mTxCertRegDRep`
                                                  {bool}
                                                  eta
                                                  (\(a : data)
                                                    (b : integer) ->
                                                     `$mTxCertRegDRep`
                                                       {bool}
                                                       v
                                                       (\(a' : data)
                                                         (b' : integer) ->
                                                          case
                                                            (all dead. bool)
                                                            (`$fEqCredential_$c==`
                                                               a
                                                               a')
                                                            [ (/\dead -> False)
                                                            , (/\dead ->
                                                                 equalsInteger
                                                                   b
                                                                   b') ]
                                                            {all dead. dead})
                                                       (\(void : unit) ->
                                                          fail ()))
                                                  (\(void : unit) -> fail ())
                                          !fail :
                                             unit -> bool
                                            = \(ds : unit) ->
                                                `$mTxCertRegDeleg`
                                                  {bool}
                                                  eta
                                                  (\(a : data)
                                                    (b : data)
                                                    (c : integer) ->
                                                     `$mTxCertRegDeleg`
                                                       {bool}
                                                       v
                                                       (\(a' : data)
                                                         (b' : data)
                                                         (c' : integer) ->
                                                          case
                                                            (all dead. bool)
                                                            (`$fEqCredential_$c==`
                                                               a
                                                               a')
                                                            [ (/\dead -> False)
                                                            , (/\dead ->
                                                                 case
                                                                   (all dead.
                                                                      bool)
                                                                   (`$fEqDelegatee0_$c==`
                                                                      b
                                                                      b')
                                                                   [ (/\dead ->
                                                                        False)
                                                                   , (/\dead ->
                                                                        equalsInteger
                                                                          c
                                                                          c') ]
                                                                   {all dead.
                                                                      dead}) ]
                                                            {all dead. dead})
                                                       (\(void : unit) ->
                                                          fail ()))
                                                  (\(void : unit) -> fail ())
                                          !fail :
                                             unit -> bool
                                            = \(ds : unit) ->
                                                let
                                                  !tup :
                                                     pair integer (list data)
                                                    = unConstrData eta
                                                in
                                                case
                                                  (all dead. bool)
                                                  (equalsInteger
                                                     2
                                                     (case
                                                        integer
                                                        tup
                                                        [ (\(l : integer)
                                                            (r : list data) ->
                                                             l) ]))
                                                  [ (/\dead -> fail ())
                                                  , (/\dead ->
                                                       let
                                                         !l : list data
                                                           = case
                                                               (list data)
                                                               tup
                                                               [ (\(l : integer)
                                                                   (r :
                                                                      list
                                                                        data) ->
                                                                    r) ]
                                                         !tup :
                                                            pair
                                                              integer
                                                              (list data)
                                                           = unConstrData v
                                                       in
                                                       case
                                                         (all dead. bool)
                                                         (equalsInteger
                                                            2
                                                            (case
                                                               integer
                                                               tup
                                                               [ (\(l : integer)
                                                                   (r :
                                                                      list
                                                                        data) ->
                                                                    l) ]))
                                                         [ (/\dead -> fail ())
                                                         , (/\dead ->
                                                              let
                                                                !l :
                                                                   list data
                                                                  = case
                                                                      (list
                                                                         data)
                                                                      tup
                                                                      [ (\(l :
                                                                             integer)
                                                                          (r :
                                                                             list
                                                                               data) ->
                                                                           r) ]
                                                              in
                                                              case
                                                                (all dead. bool)
                                                                (`$fEqCredential_$c==`
                                                                   (headList
                                                                      {data}
                                                                      l)
                                                                   (headList
                                                                      {data}
                                                                      l))
                                                                [ (/\dead ->
                                                                     False)
                                                                , (/\dead ->
                                                                     `$fEqDelegatee0_$c==`
                                                                       (headList
                                                                          {data}
                                                                          (tailList
                                                                             {data}
                                                                             l))
                                                                       (headList
                                                                          {data}
                                                                          (tailList
                                                                             {data}
                                                                             l))) ]
                                                                {all dead.
                                                                   dead}) ]
                                                         {all dead. dead}) ]
                                                  {all dead. dead}
                                          !fail :
                                             unit -> bool
                                            = \(ds : unit) ->
                                                `$mTxCertUnRegStaking`
                                                  {bool}
                                                  eta
                                                  (\(a : data)
                                                    (b : Maybe integer) ->
                                                     `$mTxCertUnRegStaking`
                                                       {bool}
                                                       v
                                                       (\(a' : data)
                                                         (b' : Maybe integer) ->
                                                          case
                                                            (all dead. bool)
                                                            (`$fEqCredential_$c==`
                                                               a
                                                               a')
                                                            [ (/\dead -> False)
                                                            , (/\dead ->
                                                                 `$dEq` b b') ]
                                                            {all dead. dead})
                                                       (\(void : unit) ->
                                                          fail ()))
                                                  (\(void : unit) -> fail ())
                                        in
                                        `$mTxCertRegStaking`
                                          {bool}
                                          eta
                                          (\(a : data) (b : Maybe integer) ->
                                             `$mTxCertRegStaking`
                                               {bool}
                                               v
                                               (\(a' : data)
                                                 (b' : Maybe integer) ->
                                                  case
                                                    (all dead. bool)
                                                    (`$fEqCredential_$c==` a a')
                                                    [ (/\dead -> False)
                                                    , (/\dead -> `$dEq` b b') ]
                                                    {all dead. dead})
                                               (\(void : unit) -> fail ()))
                                          (\(void : unit) -> fail ()))
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
                    (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                       {data}
                       `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                       (headList {data} (tailList {data} l)))
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
                               let
                                 !v : data
                                   = headList
                                       {data}
                                       (case
                                          (list data)
                                          (unConstrData x)
                                          [ (\(l : integer) (r : list data) ->
                                               r) ])
                                 !l : data = headList {data} l
                               in
                               case
                                 (all dead. bool)
                                 (equalsByteString
                                    (txOutRefId l)
                                    (txOutRefId v))
                                 [ (/\dead -> False)
                                 , (/\dead ->
                                      equalsInteger
                                        (txOutRefIdx l)
                                        (txOutRefIdx v)) ]
                                 {all dead. dead})
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
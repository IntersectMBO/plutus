(let
    data Unit | Unit_match where
      Unit : Unit
    data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
      Tuple2 : a -> b -> Tuple2 a b
    !fail : unit -> Tuple2 data data
      = \(ds : unit) ->
          let
            !defaultBody : Tuple2 data data = error {Tuple2 data data}
          in
          Unit_match (error {Unit}) {Tuple2 data data} defaultBody
    !divCeil : integer -> integer -> integer
      = \(x : integer) (y : integer) ->
          addInteger 1 (divideInteger (subtractInteger x 1) y)
    !fail : unit -> Tuple2 data data
      = \(ds : unit) ->
          let
            !defaultBody : Tuple2 data data = error {Tuple2 data data}
          in
          Unit_match (error {Unit}) {Tuple2 data data} defaultBody
    data VestingRedeemer | VestingRedeemer_match where
      FullUnlock : VestingRedeemer
      PartialUnlock : VestingRedeemer
    !`$bPubKeyCredential` : integer = 0
    !`$bScriptCredential` : integer = 1
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
                       `$bScriptCredential`
                       (case
                          integer
                          tup
                          [(\(l : integer) (r : list data) -> l)]))
                    [ (/\dead -> False)
                    , (/\dead ->
                         let
                           !tup : pair integer (list data) = unConstrData ds
                         in
                         case
                           (all dead. bool)
                           (equalsInteger
                              `$bScriptCredential`
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
               `$bPubKeyCredential`
               (case integer tup [(\(l : integer) (r : list data) -> l)]))
            [ (/\dead -> fail ())
            , (/\dead ->
                 let
                   !tup : pair integer (list data) = unConstrData ds
                 in
                 case
                   (all dead. bool)
                   (equalsInteger
                      `$bPubKeyCredential`
                      (case
                         integer
                         tup
                         [(\(l : integer) (r : list data) -> l)]))
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
    !`$mStakingPtr` :
       all r. data -> (integer -> integer -> integer -> r) -> (unit -> r) -> r
      = /\r ->
          \(scrut : data)
           (cont : integer -> integer -> integer -> r)
           (fail : unit -> r) ->
            let
              !tup : pair integer (list data) = unConstrData scrut
            in
            case
              (all dead. r)
              (equalsInteger
                 `$bScriptCredential`
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
                     (unIData (headList {data} l))
                     (unIData (headList {data} l))
                     (unIData (headList {data} (tailList {data} l)))) ]
              {all dead. dead}
    !`$bNoOutputDatum` : integer = 0
    !`$bOutputDatum` : integer = 2
    !`$bOutputDatumHash` : integer = 1
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
    !`$mPubKeyCredential` : all r. data -> (bytestring -> r) -> (unit -> r) -> r
      = /\r ->
          \(scrut : data) (cont : bytestring -> r) (fail : unit -> r) ->
            let
              !tup : pair integer (list data) = unConstrData scrut
            in
            case
              (all dead. r)
              (equalsInteger
                 `$bPubKeyCredential`
                 (case integer tup [(\(l : integer) (r : list data) -> l)]))
              [ (/\dead -> fail ())
              , (/\dead ->
                   cont
                     (unBData
                        (headList
                           {data}
                           (case
                              (list data)
                              tup
                              [(\(l : integer) (r : list data) -> r)])))) ]
              {all dead. dead}
    !`$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData` : data -> data
      = \(d : data) -> d
    !casePair : all a b r. pair a b -> (a -> b -> r) -> r
      = /\a b r -> \(p : pair a b) (f : a -> b -> r) -> case r p [f]
    data (Maybe :: * -> *) a | Maybe_match where
      Just : a -> Maybe a
      Nothing : Maybe a
    !`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData` :
       all a. (\a -> data -> a) a -> data -> Maybe a
      = /\a ->
          \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
            casePair
              {integer}
              {list data}
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
    !`$mSpendingScript` :
       all r. data -> (data -> Maybe data -> r) -> (unit -> r) -> r
      = /\r ->
          \(scrut : data) (cont : data -> Maybe data -> r) (fail : unit -> r) ->
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
                        {data}
                        `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                        (headList {data} (tailList {data} l)))) ]
              {all dead. dead}
    !`/=` : all a. (\a -> a -> a -> bool) a -> a -> a -> bool
      = /\a ->
          \(`$dEq` : (\a -> a -> a -> bool) a) (x : a) (y : a) ->
            case bool (`$dEq` x y) [True, False]
    data (Solo :: * -> *) a | Solo_match where
      MkSolo : a -> Solo a
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
    !assetClassValueOf :
       (\k a -> list (pair data data))
         bytestring
         ((\k a -> list (pair data data)) bytestring integer) ->
       Tuple2 bytestring bytestring ->
       integer
      = \(v :
            (\k a -> list (pair data data))
              bytestring
              ((\k a -> list (pair data data)) bytestring integer))
         (ds : Tuple2 bytestring bytestring) ->
          Tuple2_match
            {bytestring}
            {bytestring}
            ds
            {integer}
            (\(c : bytestring) (t : bytestring) ->
               Maybe_match
                 {data}
                 (lookup' (bData c) v)
                 {integer}
                 (\(a : data) ->
                    let
                      !m : list (pair data data) = unMapData a
                    in
                    Maybe_match
                      {data}
                      (lookup' (bData t) m)
                      {integer}
                      (\(a : data) -> unIData a)
                      0)
                 0)
    data VestingDatum | VestingDatum_match where
      VestingDatum :
        data ->
        Tuple2 bytestring bytestring ->
        integer ->
        integer ->
        integer ->
        integer ->
        integer ->
        VestingDatum
    !beneficiary : VestingDatum -> data
      = \(ds : VestingDatum) ->
          VestingDatum_match
            ds
            {data}
            (\(ds : data)
              (ds : Tuple2 bytestring bytestring)
              (ds : integer)
              (ds : integer)
              (ds : integer)
              (ds : integer)
              (ds : integer) ->
               ds)
    !`$mScriptCredential` : all r. data -> (bytestring -> r) -> (unit -> r) -> r
      = /\r ->
          \(scrut : data) (cont : bytestring -> r) (fail : unit -> r) ->
            let
              !tup : pair integer (list data) = unConstrData scrut
            in
            case
              (all dead. r)
              (equalsInteger
                 `$bScriptCredential`
                 (case integer tup [(\(l : integer) (r : list data) -> l)]))
              [ (/\dead -> fail ())
              , (/\dead ->
                   cont
                     (unBData
                        (headList
                           {data}
                           (case
                              (list data)
                              tup
                              [(\(l : integer) (r : list data) -> r)])))) ]
              {all dead. dead}
    !addressCredential : data -> data
      = \(ds : data) ->
          headList
            {data}
            (case
               (list data)
               (unConstrData ds)
               [(\(l : integer) (r : list data) -> r)])
    !traceError : all a. string -> a
      = /\a ->
          \(str : string) -> let !x : Unit = trace {Unit} str Unit in error {a}
    !getLowerInclusiveTimeRange : (\a -> data) integer -> integer
      = \(ds : (\a -> data) integer) ->
          let
            !l : list data
              = case
                  (list data)
                  (unConstrData
                     (headList
                        {data}
                        (case
                           (list data)
                           (unConstrData ds)
                           [(\(l : integer) (r : list data) -> r)])))
                  [(\(l : integer) (r : list data) -> r)]
            !tup : pair integer (list data) = unConstrData (headList {data} l)
          in
          case
            (all dead. integer)
            (equalsInteger
               1
               (case integer tup [(\(l : integer) (r : list data) -> l)]))
            [ (/\dead -> traceError {integer} "Time range not Finite")
            , (/\dead ->
                 let
                   !posixTime : integer
                     = unIData
                         (headList
                            {data}
                            (case
                               (list data)
                               tup
                               [(\(l : integer) (r : list data) -> r)]))
                 in
                 case
                   (all dead. integer)
                   (casePair
                      {integer}
                      {list data}
                      {bool}
                      (unConstrData (headList {data} (tailList {data} l)))
                      (\(index : integer) (args : list data) ->
                         case
                           (list data -> bool)
                           index
                           [ (\(ds : list data) -> False)
                           , (\(ds : list data) -> True) ]
                           args))
                   [(/\dead -> addInteger 1 posixTime), (/\dead -> posixTime)]
                   {all dead. dead}) ]
            {all dead. dead}
    !greaterThanEqualsInteger : integer -> integer -> bool
      = \(x : integer) (y : integer) ->
          case bool (lessThanInteger x y) [True, False]
    !`$mScriptContext` :
       all r. data -> (data -> data -> data -> r) -> (unit -> r) -> r
      = /\r ->
          \(scrut : data)
           (cont : data -> data -> data -> r)
           (fail : unit -> r) ->
            let
              !l : list data
                = case
                    (list data)
                    (unConstrData scrut)
                    [(\(l : integer) (r : list data) -> r)]
              !l : list data = tailList {data} l
            in
            cont
              (headList {data} l)
              (headList {data} l)
              (headList {data} (tailList {data} l))
    !scriptContextScriptInfo : data -> data
      = \(ds : data) ->
          `$mScriptContext`
            {data}
            ds
            (\(ds : data) (ds : data) (ds : data) -> ds)
            (\(void : unit) -> error {data})
    !scriptContextTxInfo : data -> data
      = \(ds : data) ->
          `$mScriptContext`
            {data}
            ds
            (\(ds : data) (ds : data) (ds : data) -> ds)
            (\(void : unit) -> error {data})
    !subtractInteger : integer -> integer -> integer
      = \(x : integer) (y : integer) -> subtractInteger x y
    !totalInstallments : VestingDatum -> integer
      = \(ds : VestingDatum) ->
          VestingDatum_match
            ds
            {integer}
            (\(ds : data)
              (ds : Tuple2 bytestring bytestring)
              (ds : integer)
              (ds : integer)
              (ds : integer)
              (ds : integer)
              (ds : integer) ->
               ds)
    !txInInfoResolved : data -> data
      = \(ds : data) ->
          headList
            {data}
            (tailList
               {data}
               (case
                  (list data)
                  (unConstrData ds)
                  [(\(l : integer) (r : list data) -> r)]))
    !`$mTxInfo` :
       all r.
         data ->
         ((\a -> list data) data ->
          (\a -> list data) data ->
          (\a -> list data) data ->
          integer ->
          (\k a -> list (pair data data))
            bytestring
            ((\k a -> list (pair data data)) bytestring integer) ->
          (\a -> list data) data ->
          (\k a -> list (pair data data)) data integer ->
          (\a -> data) integer ->
          (\a -> list data) bytestring ->
          (\k a -> list (pair data data)) data data ->
          (\k a -> list (pair data data)) bytestring data ->
          bytestring ->
          (\k a -> list (pair data data))
            data
            ((\k a -> list (pair data data)) data data) ->
          (\a -> list data) data ->
          Maybe integer ->
          Maybe integer ->
          r) ->
         (unit -> r) ->
         r
      = /\r ->
          \(scrut : data)
           (cont :
              (\a -> list data) data ->
              (\a -> list data) data ->
              (\a -> list data) data ->
              integer ->
              (\k a -> list (pair data data))
                bytestring
                ((\k a -> list (pair data data)) bytestring integer) ->
              (\a -> list data) data ->
              (\k a -> list (pair data data)) data integer ->
              (\a -> data) integer ->
              (\a -> list data) bytestring ->
              (\k a -> list (pair data data)) data data ->
              (\k a -> list (pair data data)) bytestring data ->
              bytestring ->
              (\k a -> list (pair data data))
                data
                ((\k a -> list (pair data data)) data data) ->
              (\a -> list data) data ->
              Maybe integer ->
              Maybe integer ->
              r)
           (fail : unit -> r) ->
            let
              !l : list data
                = case
                    (list data)
                    (unConstrData scrut)
                    [(\(l : integer) (r : list data) -> r)]
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
            in
            cont
              (unListData (headList {data} l))
              (unListData (headList {data} l))
              (unListData (headList {data} l))
              (unIData (headList {data} l))
              (unMapData (headList {data} l))
              (unListData (headList {data} l))
              (unMapData (headList {data} l))
              (headList {data} l)
              (unListData (headList {data} l))
              (unMapData (headList {data} l))
              (unMapData (headList {data} l))
              (unBData (headList {data} l))
              (unMapData (headList {data} l))
              (unListData (headList {data} l))
              (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                 {integer}
                 unIData
                 (headList {data} l))
              (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                 {integer}
                 unIData
                 (headList {data} (tailList {data} l)))
    !txInfoValidRange : data -> (\a -> data) integer
      = \(ds : data) ->
          `$mTxInfo`
            {(\a -> data) integer}
            ds
            (\(ds : (\a -> list data) data)
              (ds : (\a -> list data) data)
              (ds : (\a -> list data) data)
              (ds : integer)
              (ds :
                 (\k a -> list (pair data data))
                   bytestring
                   ((\k a -> list (pair data data)) bytestring integer))
              (ds : (\a -> list data) data)
              (ds : (\k a -> list (pair data data)) data integer)
              (ds : (\a -> data) integer)
              (ds : (\a -> list data) bytestring)
              (ds : (\k a -> list (pair data data)) data data)
              (ds : (\k a -> list (pair data data)) bytestring data)
              (ds : bytestring)
              (ds :
                 (\k a -> list (pair data data))
                   data
                   ((\k a -> list (pair data data)) data data))
              (ds : (\a -> list data) data)
              (ds : Maybe integer)
              (ds : Maybe integer) ->
               ds)
            (\(void : unit) -> error {(\a -> data) integer})
    !`$mTxOut` :
       all r.
         data ->
         (data ->
          (\k a -> list (pair data data))
            bytestring
            ((\k a -> list (pair data data)) bytestring integer) ->
          data ->
          Maybe bytestring ->
          r) ->
         (unit -> r) ->
         r
      = /\r ->
          \(scrut : data)
           (cont :
              data ->
              (\k a -> list (pair data data))
                bytestring
                ((\k a -> list (pair data data)) bytestring integer) ->
              data ->
              Maybe bytestring ->
              r)
           (fail : unit -> r) ->
            let
              !l : list data
                = case
                    (list data)
                    (unConstrData scrut)
                    [(\(l : integer) (r : list data) -> r)]
              !l : list data = tailList {data} l
              !l : list data = tailList {data} l
            in
            cont
              (headList {data} l)
              (unMapData (headList {data} l))
              (headList {data} l)
              (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                 {bytestring}
                 unBData
                 (headList {data} (tailList {data} l)))
    !txOutAddress : data -> data
      = \(ds : data) ->
          `$mTxOut`
            {data}
            ds
            (\(ds : data)
              (ds :
                 (\k a -> list (pair data data))
                   bytestring
                   ((\k a -> list (pair data data)) bytestring integer))
              (ds : data)
              (ds : Maybe bytestring) ->
               ds)
            (\(void : unit) -> error {data})
    !txOutDatum : data -> data
      = \(ds : data) ->
          `$mTxOut`
            {data}
            ds
            (\(ds : data)
              (ds :
                 (\k a -> list (pair data data))
                   bytestring
                   ((\k a -> list (pair data data)) bytestring integer))
              (ds : data)
              (ds : Maybe bytestring) ->
               ds)
            (\(void : unit) -> error {data})
    !txOutValue :
       data ->
       (\k a -> list (pair data data))
         bytestring
         ((\k a -> list (pair data data)) bytestring integer)
      = \(ds : data) ->
          unMapData
            (headList
               {data}
               (tailList
                  {data}
                  (case
                     (list data)
                     (unConstrData ds)
                     [(\(l : integer) (r : list data) -> r)])))
    !find :
       all a.
         (\a -> data -> a) a -> (a -> bool) -> (\a -> list data) a -> Maybe a
      = /\a ->
          \(`$dUnsafeFromData` : (\a -> data -> a) a) (pred' : a -> bool) ->
            letrec
              !go : (\a -> list data) a -> Maybe a
                = \(ds : (\a -> list data) a) ->
                    case
                      (Maybe a)
                      ds
                      [ (\(x : data) (eta : list data) ->
                           let
                             !h : a = `$dUnsafeFromData` x
                           in
                           case
                             (all dead. Maybe a)
                             (pred' h)
                             [(/\dead -> go eta), (/\dead -> Just {a} h)]
                             {all dead. dead})
                      , (Nothing {a}) ]
            in
            \(eta : (\a -> list data) a) -> go eta
    !txSignedBy : data -> bytestring -> bool
      = \(ds : data) (k : bytestring) ->
          `$mTxInfo`
            {bool}
            ds
            (\(ds : (\a -> list data) data)
              (ds : (\a -> list data) data)
              (ds : (\a -> list data) data)
              (ds : integer)
              (ds :
                 (\k a -> list (pair data data))
                   bytestring
                   ((\k a -> list (pair data data)) bytestring integer))
              (ds : (\a -> list data) data)
              (ds : (\k a -> list (pair data data)) data integer)
              (ds : (\a -> data) integer)
              (ds : (\a -> list data) bytestring)
              (ds : (\k a -> list (pair data data)) data data)
              (ds : (\k a -> list (pair data data)) bytestring data)
              (ds : bytestring)
              (ds :
                 (\k a -> list (pair data data))
                   data
                   ((\k a -> list (pair data data)) data data))
              (ds : (\a -> list data) data)
              (ds : Maybe integer)
              (ds : Maybe integer) ->
               Maybe_match
                 {bytestring}
                 (find
                    {bytestring}
                    unBData
                    (\(y : bytestring) -> equalsByteString k y)
                    ds)
                 {bool}
                 (\(ds : bytestring) -> True)
                 False)
            (\(void : unit) ->
               let
                 !defaultBody : bool = error {bool}
               in
               Unit_match (error {Unit}) {bool} defaultBody)
    !vestingPeriodEnd : VestingDatum -> integer
      = \(ds : VestingDatum) ->
          VestingDatum_match
            ds
            {integer}
            (\(ds : data)
              (ds : Tuple2 bytestring bytestring)
              (ds : integer)
              (ds : integer)
              (ds : integer)
              (ds : integer)
              (ds : integer) ->
               ds)
  in
  \(scriptContextData : data) ->
    Maybe_match
      {data}
      (trace
         {Maybe data}
         "Parsing ScriptContext..."
         (Just {data} scriptContextData))
      {all dead. unit}
      (\(ctx : data) ->
         /\dead ->
           case
             (all dead. unit)
             (let
               !context : data = trace {data} "Parsed ScriptContext" ctx
             in
             trace
               {bool}
               "Validation completed"
               (VestingRedeemer_match
                  (Maybe_match
                     {VestingRedeemer}
                     (let
                       !d : data
                         = `$mScriptContext`
                             {data}
                             context
                             (\(ds : data) (ds : data) (ds : data) -> ds)
                             (\(void : unit) -> error {data})
                     in
                     chooseData
                       {Unit -> Maybe VestingRedeemer}
                       d
                       (\(ds : Unit) ->
                          casePair
                            {integer}
                            {list data}
                            {Maybe VestingRedeemer}
                            (unConstrData d)
                            (\(l : integer) (r : list data) ->
                               case
                                 (all dead. Maybe VestingRedeemer)
                                 (equalsInteger 0 l)
                                 [ (/\dead ->
                                      case
                                        (all dead. Maybe VestingRedeemer)
                                        (equalsInteger 1 l)
                                        [ (/\dead -> Nothing {VestingRedeemer})
                                        , (/\dead ->
                                             Just
                                               {VestingRedeemer}
                                               FullUnlock) ]
                                        {all dead. dead})
                                 , (/\dead ->
                                      Just {VestingRedeemer} PartialUnlock) ]
                                 {all dead. dead}))
                       (\(ds : Unit) -> Nothing {VestingRedeemer})
                       (\(ds : Unit) -> Nothing {VestingRedeemer})
                       (\(ds : Unit) -> Nothing {VestingRedeemer})
                       (\(ds : Unit) -> Nothing {VestingRedeemer})
                       Unit)
                     {all dead. VestingRedeemer}
                     (\(r : VestingRedeemer) ->
                        /\dead -> trace {VestingRedeemer} "Parsed Redeemer" r)
                     (/\dead ->
                        let
                          !x : Unit
                            = trace {Unit} "Failed to parse Redeemer" Unit
                        in
                        error {VestingRedeemer})
                     {all dead. dead})
                  {all dead. bool}
                  (/\dead ->
                     let
                       !ctx : data
                         = trace {data} "Full unlock requested" context
                     in
                     Tuple2_match
                       {data}
                       {data}
                       (let
                         !nt : data = scriptContextScriptInfo ctx
                       in
                       `$mSpendingScript`
                         {Tuple2 data data}
                         nt
                         (\(_ownRef : data) (ds : Maybe data) ->
                            Maybe_match
                              {data}
                              ds
                              {all dead. Tuple2 data data}
                              (\(ds : data) ->
                                 /\dead -> Tuple2 {data} {data} _ownRef ds)
                              (/\dead -> fail ())
                              {all dead. dead})
                         (\(void : unit) -> fail ()))
                       {bool}
                       (\(ipv : data)
                         (ipv : data) ->
                          let
                            !ds : Solo VestingDatum
                              = MkSolo
                                  {VestingDatum}
                                  (casePair
                                     {integer}
                                     {list data}
                                     {VestingDatum}
                                     (unConstrData ipv)
                                     (\(index : integer) (args : list data) ->
                                        case
                                          (list data -> VestingDatum)
                                          index
                                          [ (\(ds : list data) ->
                                               let
                                                 !l : list data
                                                   = tailList {data} ds
                                                 !l : list data
                                                   = tailList {data} l
                                                 !l : list data
                                                   = tailList {data} l
                                                 !l : list data
                                                   = tailList {data} l
                                                 !l : list data
                                                   = tailList {data} l
                                               in
                                               VestingDatum
                                                 (headList {data} ds)
                                                 (let
                                                   !d : data = headList {data} l
                                                 in
                                                 casePair
                                                   {integer}
                                                   {list data}
                                                   {Tuple2
                                                      bytestring
                                                      bytestring}
                                                   (unConstrData d)
                                                   (\(index : integer)
                                                     (args : list data) ->
                                                      case
                                                        (list data ->
                                                         Tuple2
                                                           bytestring
                                                           bytestring)
                                                        index
                                                        [ (\(ds : list data) ->
                                                             Tuple2
                                                               {bytestring}
                                                               {bytestring}
                                                               (unBData
                                                                  (headList
                                                                     {data}
                                                                     ds))
                                                               (unBData
                                                                  (headList
                                                                     {data}
                                                                     (tailList
                                                                        {data}
                                                                        ds)))) ]
                                                        args))
                                                 (unIData (headList {data} l))
                                                 (unIData (headList {data} l))
                                                 (unIData (headList {data} l))
                                                 (unIData (headList {data} l))
                                                 (unIData
                                                    (headList
                                                       {data}
                                                       (tailList {data} l)))) ]
                                          args))
                            !vestingDatum : VestingDatum
                              = Solo_match
                                  {VestingDatum}
                                  ds
                                  {VestingDatum}
                                  (\(vestingDatum : VestingDatum) ->
                                     vestingDatum)
                          in
                          Solo_match
                            {bytestring}
                            (let
                              !nt : data
                                = addressCredential (beneficiary vestingDatum)
                            in
                            `$mPubKeyCredential`
                              {Solo bytestring}
                              nt
                              (\(beneficiaryKey : bytestring) ->
                                 MkSolo {bytestring} beneficiaryKey)
                              (\(void : unit) ->
                                 let
                                   !defaultBody : Solo bytestring
                                     = error {Solo bytestring}
                                 in
                                 Unit_match
                                   (error {Unit})
                                   {Solo bytestring}
                                   defaultBody))
                            {bool}
                            (\(ipv : bytestring) ->
                               let
                                 !ds : Solo data
                                   = MkSolo {data} (scriptContextTxInfo ctx)
                                 !txInfo : data
                                   = Solo_match
                                       {data}
                                       ds
                                       {data}
                                       (\(txInfo : data) -> txInfo)
                                 !ds : integer
                                   = getLowerInclusiveTimeRange
                                       (txInfoValidRange txInfo)
                               in
                               case
                                 (all dead. bool)
                                 (case
                                    bool
                                    (txSignedBy txInfo ipv)
                                    [True, False])
                                 [ (/\dead ->
                                      case
                                        (all dead. bool)
                                        (greaterThanEqualsInteger
                                           (vestingPeriodEnd vestingDatum)
                                           ds)
                                        [ (/\dead -> True)
                                        , (/\dead ->
                                             traceError
                                               {bool}
                                               "Unlock not permitted until vestingPeriodEnd time") ]
                                        {all dead. dead})
                                 , (/\dead ->
                                      traceError
                                        {bool}
                                        "Missing beneficiary signature") ]
                                 {all dead. dead})))
                  (/\dead ->
                     let
                       !ctx : data
                         = trace {data} "Partial unlock requested" context
                     in
                     Tuple2_match
                       {data}
                       {data}
                       (let
                         !nt : data = scriptContextScriptInfo ctx
                       in
                       `$mSpendingScript`
                         {Tuple2 data data}
                         nt
                         (\(ownRef : data) (ds : Maybe data) ->
                            Maybe_match
                              {data}
                              ds
                              {all dead. Tuple2 data data}
                              (\(ds : data) ->
                                 /\dead -> Tuple2 {data} {data} ownRef ds)
                              (/\dead -> fail ())
                              {all dead. dead})
                         (\(void : unit) -> fail ()))
                       {bool}
                       (\(ipv : data)
                         (ipv : data) ->
                          let
                            !ds : Solo VestingDatum
                              = MkSolo
                                  {VestingDatum}
                                  (casePair
                                     {integer}
                                     {list data}
                                     {VestingDatum}
                                     (unConstrData ipv)
                                     (\(index : integer) (args : list data) ->
                                        case
                                          (list data -> VestingDatum)
                                          index
                                          [ (\(ds : list data) ->
                                               let
                                                 !l : list data
                                                   = tailList {data} ds
                                                 !l : list data
                                                   = tailList {data} l
                                                 !l : list data
                                                   = tailList {data} l
                                                 !l : list data
                                                   = tailList {data} l
                                                 !l : list data
                                                   = tailList {data} l
                                               in
                                               VestingDatum
                                                 (headList {data} ds)
                                                 (let
                                                   !d : data = headList {data} l
                                                 in
                                                 casePair
                                                   {integer}
                                                   {list data}
                                                   {Tuple2
                                                      bytestring
                                                      bytestring}
                                                   (unConstrData d)
                                                   (\(index : integer)
                                                     (args : list data) ->
                                                      case
                                                        (list data ->
                                                         Tuple2
                                                           bytestring
                                                           bytestring)
                                                        index
                                                        [ (\(ds : list data) ->
                                                             Tuple2
                                                               {bytestring}
                                                               {bytestring}
                                                               (unBData
                                                                  (headList
                                                                     {data}
                                                                     ds))
                                                               (unBData
                                                                  (headList
                                                                     {data}
                                                                     (tailList
                                                                        {data}
                                                                        ds)))) ]
                                                        args))
                                                 (unIData (headList {data} l))
                                                 (unIData (headList {data} l))
                                                 (unIData (headList {data} l))
                                                 (unIData (headList {data} l))
                                                 (unIData
                                                    (headList
                                                       {data}
                                                       (tailList {data} l)))) ]
                                          args))
                            !vestingDatum : VestingDatum
                              = Solo_match
                                  {VestingDatum}
                                  ds
                                  {VestingDatum}
                                  (\(vestingDatum : VestingDatum) ->
                                     vestingDatum)
                            !ds : Solo (Tuple2 bytestring bytestring)
                              = MkSolo
                                  {Tuple2 bytestring bytestring}
                                  (VestingDatum_match
                                     vestingDatum
                                     {Tuple2 bytestring bytestring}
                                     (\(ds : data)
                                       (ds : Tuple2 bytestring bytestring)
                                       (ds : integer)
                                       (ds : integer)
                                       (ds : integer)
                                       (ds : integer)
                                       (ds : integer) ->
                                        ds))
                            ~asset : Tuple2 bytestring bytestring
                              = Solo_match
                                  {Tuple2 bytestring bytestring}
                                  ds
                                  {Tuple2 bytestring bytestring}
                                  (\(asset : Tuple2 bytestring bytestring) ->
                                     asset)
                            !ds : integer
                              = divCeil
                                  (subtractInteger
                                     (vestingPeriodEnd vestingDatum)
                                     (VestingDatum_match
                                        vestingDatum
                                        {integer}
                                        (\(ds : data)
                                          (ds : Tuple2 bytestring bytestring)
                                          (ds : integer)
                                          (ds : integer)
                                          (ds : integer)
                                          (ds : integer)
                                          (ds : integer) ->
                                           ds)))
                                  (totalInstallments vestingDatum)
                          in
                          Solo_match
                            {bytestring}
                            (let
                              !nt : data
                                = addressCredential (beneficiary vestingDatum)
                            in
                            `$mPubKeyCredential`
                              {Solo bytestring}
                              nt
                              (\(beneficiaryHash : bytestring) ->
                                 MkSolo {bytestring} beneficiaryHash)
                              (\(void : unit) ->
                                 let
                                   !defaultBody : Solo bytestring
                                     = error {Solo bytestring}
                                 in
                                 Unit_match
                                   (error {Unit})
                                   {Solo bytestring}
                                   defaultBody))
                            {bool}
                            (\(ipv : bytestring) ->
                               let
                                 !ds : Solo data
                                   = MkSolo {data} (scriptContextTxInfo ctx)
                                 !txInfo : data
                                   = Solo_match
                                       {data}
                                       ds
                                       {data}
                                       (\(txInfo : data) -> txInfo)
                                 !nt : list data
                                   = `$mTxInfo`
                                       {(\a -> list data) data}
                                       txInfo
                                       (\(ds : (\a -> list data) data)
                                         (ds : (\a -> list data) data)
                                         (ds : (\a -> list data) data)
                                         (ds : integer)
                                         (ds :
                                            (\k a -> list (pair data data))
                                              bytestring
                                              ((\k a -> list (pair data data))
                                                 bytestring
                                                 integer))
                                         (ds : (\a -> list data) data)
                                         (ds :
                                            (\k a -> list (pair data data))
                                              data
                                              integer)
                                         (ds : (\a -> data) integer)
                                         (ds : (\a -> list data) bytestring)
                                         (ds :
                                            (\k a -> list (pair data data))
                                              data
                                              data)
                                         (ds :
                                            (\k a -> list (pair data data))
                                              bytestring
                                              data)
                                         (ds : bytestring)
                                         (ds :
                                            (\k a -> list (pair data data))
                                              data
                                              ((\k a -> list (pair data data))
                                                 data
                                                 data))
                                         (ds : (\a -> list data) data)
                                         (ds : Maybe integer)
                                         (ds : Maybe integer) ->
                                          ds)
                                       (\(void : unit) ->
                                          error {(\a -> list data) data})
                                 !ds :
                                    Solo data
                                   = Maybe_match
                                       {data}
                                       (find
                                          {data}
                                          `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                          (\(eta : data) ->
                                             let
                                               !l : data
                                                 = headList
                                                     {data}
                                                     (case
                                                        (list data)
                                                        (unConstrData eta)
                                                        [ (\(l : integer)
                                                            (r : list data) ->
                                                             r) ])
                                             in
                                             case
                                               (all dead. bool)
                                               (equalsByteString
                                                  (txOutRefId l)
                                                  (txOutRefId ipv))
                                               [ (/\dead -> False)
                                               , (/\dead ->
                                                    equalsInteger
                                                      (txOutRefIdx l)
                                                      (txOutRefIdx ipv)) ]
                                               {all dead. dead})
                                          nt)
                                       {all dead. Solo data}
                                       (\(ownVestingInput : data) ->
                                          /\dead ->
                                            MkSolo {data} ownVestingInput)
                                       (/\dead ->
                                          let
                                            !defaultBody : Solo data
                                              = error {Solo data}
                                          in
                                          Unit_match
                                            (error {Unit})
                                            {Solo data}
                                            defaultBody)
                                       {all dead. dead}
                               in
                               Solo_match
                                 {data}
                                 ds
                                 {bool}
                                 (\(ipv : data) ->
                                    let
                                      !nt : data = txInInfoResolved ipv
                                      !nt : data = txOutAddress nt
                                    in
                                    Solo_match
                                      {bytestring}
                                      (let
                                        !nt : data = addressCredential nt
                                      in
                                      `$mScriptCredential`
                                        {Solo bytestring}
                                        nt
                                        (\(scriptHash : bytestring) ->
                                           MkSolo {bytestring} scriptHash)
                                        (\(void : unit) ->
                                           let
                                             !defaultBody : Solo bytestring
                                               = error {Solo bytestring}
                                           in
                                           Unit_match
                                             (error {Unit})
                                             {Solo bytestring}
                                             defaultBody))
                                      {bool}
                                      (\(ipv : bytestring) ->
                                         letrec
                                           !go :
                                              integer ->
                                              (\a -> list data) data ->
                                              integer
                                             = \(n : integer)
                                                (ds : (\a -> list data) data) ->
                                                 case
                                                   integer
                                                   ds
                                                   [ (\(x : data)
                                                       (eta : list data) ->
                                                        let
                                                          !nt :
                                                             data
                                                            = addressCredential
                                                                (txOutAddress
                                                                   (txInInfoResolved
                                                                      x))
                                                        in
                                                        `$mScriptCredential`
                                                          {integer}
                                                          nt
                                                          (\(vh : bytestring) ->
                                                             case
                                                               (all dead.
                                                                  integer)
                                                               (equalsByteString
                                                                  vh
                                                                  ipv)
                                                               [ (/\dead ->
                                                                    go n eta)
                                                               , (/\dead ->
                                                                    go
                                                                      (addInteger
                                                                         1
                                                                         n)
                                                                      eta) ]
                                                               {all dead. dead})
                                                          (\(void : unit) ->
                                                             go n eta))
                                                   , n ]
                                         in
                                         let
                                           !ds : integer
                                             = assetClassValueOf
                                                 (txOutValue nt)
                                                 asset
                                           !ds :
                                              Solo data
                                             = Maybe_match
                                                 {data}
                                                 (find
                                                    {data}
                                                    `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                    (\(eta : data) ->
                                                       let
                                                         !l : list data
                                                           = case
                                                               (list data)
                                                               (unConstrData
                                                                  (txOutAddress
                                                                     eta))
                                                               [ (\(l : integer)
                                                                   (r :
                                                                      list
                                                                        data) ->
                                                                    r) ]
                                                         !l : list data
                                                           = case
                                                               (list data)
                                                               (unConstrData nt)
                                                               [ (\(l : integer)
                                                                   (r :
                                                                      list
                                                                        data) ->
                                                                    r) ]
                                                       in
                                                       case
                                                         (all dead. bool)
                                                         (`$fEqCredential_$c==`
                                                            (headList {data} l)
                                                            (headList {data} l))
                                                         [ (/\dead -> False)
                                                         , (/\dead ->
                                                              Maybe_match
                                                                {data}
                                                                (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                   {data}
                                                                   `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                   (headList
                                                                      {data}
                                                                      (tailList
                                                                         {data}
                                                                         l)))
                                                                {all dead. bool}
                                                                (\(a : data) ->
                                                                   /\dead ->
                                                                     Maybe_match
                                                                       {data}
                                                                       (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                          {data}
                                                                          `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                          (headList
                                                                             {data}
                                                                             (tailList
                                                                                {data}
                                                                                l)))
                                                                       {bool}
                                                                       (\(a :
                                                                            data) ->
                                                                          let
                                                                            !fail :
                                                                               unit ->
                                                                               bool
                                                                              = \(ds :
                                                                                    unit) ->
                                                                                  `$mStakingPtr`
                                                                                    {bool}
                                                                                    a
                                                                                    (\(a :
                                                                                         integer)
                                                                                      (b :
                                                                                         integer)
                                                                                      (c :
                                                                                         integer) ->
                                                                                       `$mStakingPtr`
                                                                                         {bool}
                                                                                         a
                                                                                         (\(a' :
                                                                                              integer)
                                                                                           (b' :
                                                                                              integer)
                                                                                           (c' :
                                                                                              integer) ->
                                                                                            case
                                                                                              (all dead.
                                                                                                 bool)
                                                                                              (equalsInteger
                                                                                                 a
                                                                                                 a')
                                                                                              [ (/\dead ->
                                                                                                   False)
                                                                                              , (/\dead ->
                                                                                                   case
                                                                                                     (all dead.
                                                                                                        bool)
                                                                                                     (equalsInteger
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
                                                                                              {all dead.
                                                                                                 dead})
                                                                                         (\(void :
                                                                                              unit) ->
                                                                                            False))
                                                                                    (\(void :
                                                                                         unit) ->
                                                                                       False)
                                                                            !tup :
                                                                               pair
                                                                                 integer
                                                                                 (list
                                                                                    data)
                                                                              = unConstrData
                                                                                  a
                                                                          in
                                                                          case
                                                                            (all dead.
                                                                               bool)
                                                                            (equalsInteger
                                                                               `$bPubKeyCredential`
                                                                               (case
                                                                                  integer
                                                                                  tup
                                                                                  [ (\(l :
                                                                                         integer)
                                                                                      (r :
                                                                                         list
                                                                                           data) ->
                                                                                       l) ]))
                                                                            [ (/\dead ->
                                                                                 fail
                                                                                   ())
                                                                            , (/\dead ->
                                                                                 let
                                                                                   !tup :
                                                                                      pair
                                                                                        integer
                                                                                        (list
                                                                                           data)
                                                                                     = unConstrData
                                                                                         a
                                                                                 in
                                                                                 case
                                                                                   (all dead.
                                                                                      bool)
                                                                                   (equalsInteger
                                                                                      `$bPubKeyCredential`
                                                                                      (case
                                                                                         integer
                                                                                         tup
                                                                                         [ (\(l :
                                                                                                integer)
                                                                                             (r :
                                                                                                list
                                                                                                  data) ->
                                                                                              l) ]))
                                                                                   [ (/\dead ->
                                                                                        fail
                                                                                          ())
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
                                                                                   {all dead.
                                                                                      dead}) ]
                                                                            {all dead.
                                                                               dead})
                                                                       False)
                                                                (/\dead ->
                                                                   Maybe_match
                                                                     {data}
                                                                     (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                        {data}
                                                                        `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                        (headList
                                                                           {data}
                                                                           (tailList
                                                                              {data}
                                                                              l)))
                                                                     {bool}
                                                                     (\(ipv :
                                                                          data) ->
                                                                        False)
                                                                     True)
                                                                {all dead.
                                                                   dead}) ]
                                                         {all dead. dead})
                                                    (`$mTxInfo`
                                                       {(\a -> list data) data}
                                                       txInfo
                                                       (\(ds :
                                                            (\a -> list data)
                                                              data)
                                                         (ds :
                                                            (\a -> list data)
                                                              data)
                                                         (ds :
                                                            (\a -> list data)
                                                              data)
                                                         (ds : integer)
                                                         (ds :
                                                            (\k a ->
                                                               list
                                                                 (pair
                                                                    data
                                                                    data))
                                                              bytestring
                                                              ((\k a ->
                                                                  list
                                                                    (pair
                                                                       data
                                                                       data))
                                                                 bytestring
                                                                 integer))
                                                         (ds :
                                                            (\a -> list data)
                                                              data)
                                                         (ds :
                                                            (\k a ->
                                                               list
                                                                 (pair
                                                                    data
                                                                    data))
                                                              data
                                                              integer)
                                                         (ds :
                                                            (\a -> data)
                                                              integer)
                                                         (ds :
                                                            (\a -> list data)
                                                              bytestring)
                                                         (ds :
                                                            (\k a ->
                                                               list
                                                                 (pair
                                                                    data
                                                                    data))
                                                              data
                                                              data)
                                                         (ds :
                                                            (\k a ->
                                                               list
                                                                 (pair
                                                                    data
                                                                    data))
                                                              bytestring
                                                              data)
                                                         (ds : bytestring)
                                                         (ds :
                                                            (\k a ->
                                                               list
                                                                 (pair
                                                                    data
                                                                    data))
                                                              data
                                                              ((\k a ->
                                                                  list
                                                                    (pair
                                                                       data
                                                                       data))
                                                                 data
                                                                 data))
                                                         (ds :
                                                            (\a -> list data)
                                                              data)
                                                         (ds : Maybe integer)
                                                         (ds : Maybe integer) ->
                                                          ds)
                                                       (\(void : unit) ->
                                                          error
                                                            {(\a -> list data)
                                                               data})))
                                                 {all dead. Solo data}
                                                 (\(ownVestingOutput : data) ->
                                                    /\dead ->
                                                      MkSolo
                                                        {data}
                                                        ownVestingOutput)
                                                 (/\dead ->
                                                    let
                                                      !defaultBody : Solo data
                                                        = error {Solo data}
                                                    in
                                                    Unit_match
                                                      (error {Unit})
                                                      {Solo data}
                                                      defaultBody)
                                                 {all dead. dead}
                                           !ownVestingOutput : data
                                             = Solo_match
                                                 {data}
                                                 ds
                                                 {data}
                                                 (\(ownVestingOutput : data) ->
                                                    ownVestingOutput)
                                           !nt : data
                                             = txOutDatum ownVestingOutput
                                           !ds : Solo integer
                                             = MkSolo
                                                 {integer}
                                                 (assetClassValueOf
                                                    (txOutValue
                                                       ownVestingOutput)
                                                    asset)
                                           ~newRemainingQty : integer
                                             = Solo_match
                                                 {integer}
                                                 ds
                                                 {integer}
                                                 (\(newRemainingQty :
                                                      integer) ->
                                                    newRemainingQty)
                                           !ds : Solo integer
                                             = MkSolo
                                                 {integer}
                                                 (getLowerInclusiveTimeRange
                                                    (txInfoValidRange txInfo))
                                           !currentTimeApproximation : integer
                                             = Solo_match
                                                 {integer}
                                                 ds
                                                 {integer}
                                                 (\(currentTimeApproximation :
                                                      integer) ->
                                                    currentTimeApproximation)
                                           !ds :
                                              integer
                                             = divCeil
                                                 (multiplyInteger
                                                    (divCeil
                                                       (subtractInteger
                                                          (vestingPeriodEnd
                                                             vestingDatum)
                                                          currentTimeApproximation)
                                                       ds)
                                                    (VestingDatum_match
                                                       vestingDatum
                                                       {integer}
                                                       (\(ds : data)
                                                         (ds :
                                                            Tuple2
                                                              bytestring
                                                              bytestring)
                                                         (ds : integer)
                                                         (ds : integer)
                                                         (ds : integer)
                                                         (ds : integer)
                                                         (ds : integer) ->
                                                          ds)))
                                                 (totalInstallments
                                                    vestingDatum)
                                         in
                                         case
                                           (all dead. bool)
                                           (case
                                              bool
                                              (txSignedBy txInfo ipv)
                                              [True, False])
                                           [ (/\dead ->
                                                case
                                                  (all dead. bool)
                                                  (greaterThanEqualsInteger
                                                     (VestingDatum_match
                                                        vestingDatum
                                                        {integer}
                                                        (\(ds : data)
                                                          (ds :
                                                             Tuple2
                                                               bytestring
                                                               bytestring)
                                                          (ds : integer)
                                                          (ds : integer)
                                                          (ds : integer)
                                                          (ds : integer)
                                                          (ds : integer) ->
                                                           ds))
                                                     currentTimeApproximation)
                                                  [ (/\dead ->
                                                       case
                                                         (all dead. bool)
                                                         (lessThanEqualsInteger
                                                            newRemainingQty
                                                            0)
                                                         [ (/\dead ->
                                                              case
                                                                (all dead. bool)
                                                                (greaterThanEqualsInteger
                                                                   newRemainingQty
                                                                   ds)
                                                                [ (/\dead ->
                                                                     case
                                                                       (all dead.
                                                                          bool)
                                                                       (case
                                                                          bool
                                                                          (equalsInteger
                                                                             ds
                                                                             newRemainingQty)
                                                                          [ True
                                                                          , False ])
                                                                       [ (/\dead ->
                                                                            case
                                                                              (all dead.
                                                                                 bool)
                                                                              (`/=`
                                                                                 {data}
                                                                                 (\(ds :
                                                                                      data)
                                                                                   (ds :
                                                                                      data) ->
                                                                                    let
                                                                                      !fail :
                                                                                         unit ->
                                                                                         bool
                                                                                        = \(ds :
                                                                                              unit) ->
                                                                                            let
                                                                                              !tup :
                                                                                                 pair
                                                                                                   integer
                                                                                                   (list
                                                                                                      data)
                                                                                                = unConstrData
                                                                                                    ds
                                                                                            in
                                                                                            case
                                                                                              (all dead.
                                                                                                 bool)
                                                                                              (equalsInteger
                                                                                                 `$bOutputDatum`
                                                                                                 (case
                                                                                                    integer
                                                                                                    tup
                                                                                                    [ (\(l :
                                                                                                           integer)
                                                                                                        (r :
                                                                                                           list
                                                                                                             data) ->
                                                                                                         l) ]))
                                                                                              [ (/\dead ->
                                                                                                   False)
                                                                                              , (/\dead ->
                                                                                                   let
                                                                                                     !tup :
                                                                                                        pair
                                                                                                          integer
                                                                                                          (list
                                                                                                             data)
                                                                                                       = unConstrData
                                                                                                           ds
                                                                                                   in
                                                                                                   case
                                                                                                     (all dead.
                                                                                                        bool)
                                                                                                     (equalsInteger
                                                                                                        `$bOutputDatum`
                                                                                                        (case
                                                                                                           integer
                                                                                                           tup
                                                                                                           [ (\(l :
                                                                                                                  integer)
                                                                                                               (r :
                                                                                                                  list
                                                                                                                    data) ->
                                                                                                                l) ]))
                                                                                                     [ (/\dead ->
                                                                                                          False)
                                                                                                     , (/\dead ->
                                                                                                          equalsData
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
                                                                                                     {all dead.
                                                                                                        dead}) ]
                                                                                              {all dead.
                                                                                                 dead}
                                                                                      !fail :
                                                                                         unit ->
                                                                                         bool
                                                                                        = \(ds :
                                                                                              unit) ->
                                                                                            let
                                                                                              !tup :
                                                                                                 pair
                                                                                                   integer
                                                                                                   (list
                                                                                                      data)
                                                                                                = unConstrData
                                                                                                    ds
                                                                                            in
                                                                                            case
                                                                                              (all dead.
                                                                                                 bool)
                                                                                              (equalsInteger
                                                                                                 `$bOutputDatumHash`
                                                                                                 (case
                                                                                                    integer
                                                                                                    tup
                                                                                                    [ (\(l :
                                                                                                           integer)
                                                                                                        (r :
                                                                                                           list
                                                                                                             data) ->
                                                                                                         l) ]))
                                                                                              [ (/\dead ->
                                                                                                   fail
                                                                                                     ())
                                                                                              , (/\dead ->
                                                                                                   let
                                                                                                     !tup :
                                                                                                        pair
                                                                                                          integer
                                                                                                          (list
                                                                                                             data)
                                                                                                       = unConstrData
                                                                                                           ds
                                                                                                   in
                                                                                                   case
                                                                                                     (all dead.
                                                                                                        bool)
                                                                                                     (equalsInteger
                                                                                                        `$bOutputDatumHash`
                                                                                                        (case
                                                                                                           integer
                                                                                                           tup
                                                                                                           [ (\(l :
                                                                                                                  integer)
                                                                                                               (r :
                                                                                                                  list
                                                                                                                    data) ->
                                                                                                                l) ]))
                                                                                                     [ (/\dead ->
                                                                                                          fail
                                                                                                            ())
                                                                                                     , (/\dead ->
                                                                                                          equalsByteString
                                                                                                            (unBData
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
                                                                                                                          r) ])))
                                                                                                            (unBData
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
                                                                                                                          r) ])))) ]
                                                                                                     {all dead.
                                                                                                        dead}) ]
                                                                                              {all dead.
                                                                                                 dead}
                                                                                    in
                                                                                    case
                                                                                      (all dead.
                                                                                         bool)
                                                                                      (equalsInteger
                                                                                         `$bNoOutputDatum`
                                                                                         (case
                                                                                            integer
                                                                                            (unConstrData
                                                                                               ds)
                                                                                            [ (\(l :
                                                                                                   integer)
                                                                                                (r :
                                                                                                   list
                                                                                                     data) ->
                                                                                                 l) ]))
                                                                                      [ (/\dead ->
                                                                                           fail
                                                                                             ())
                                                                                      , (/\dead ->
                                                                                           case
                                                                                             (all dead.
                                                                                                bool)
                                                                                             (equalsInteger
                                                                                                `$bNoOutputDatum`
                                                                                                (case
                                                                                                   integer
                                                                                                   (unConstrData
                                                                                                      ds)
                                                                                                   [ (\(l :
                                                                                                          integer)
                                                                                                       (r :
                                                                                                          list
                                                                                                            data) ->
                                                                                                        l) ]))
                                                                                             [ (/\dead ->
                                                                                                  fail
                                                                                                    ())
                                                                                             , (/\dead ->
                                                                                                  True) ]
                                                                                             {all dead.
                                                                                                dead}) ]
                                                                                      {all dead.
                                                                                         dead})
                                                                                 (txOutDatum
                                                                                    nt)
                                                                                 nt)
                                                                              [ (/\dead ->
                                                                                   case
                                                                                     (all dead.
                                                                                        bool)
                                                                                     (`/=`
                                                                                        {integer}
                                                                                        (\(x :
                                                                                             integer)
                                                                                          (y :
                                                                                             integer) ->
                                                                                           equalsInteger
                                                                                             x
                                                                                             y)
                                                                                        (go
                                                                                           0
                                                                                           nt)
                                                                                        1)
                                                                                     [ (/\dead ->
                                                                                          True)
                                                                                     , (/\dead ->
                                                                                          traceError
                                                                                            {bool}
                                                                                            "Double satisfaction") ]
                                                                                     {all dead.
                                                                                        dead})
                                                                              , (/\dead ->
                                                                                   traceError
                                                                                     {bool}
                                                                                     "Datum Modification Prohibited") ]
                                                                              {all dead.
                                                                                 dead})
                                                                       , (/\dead ->
                                                                            traceError
                                                                              {bool}
                                                                              "Mismatched remaining asset") ]
                                                                       {all dead.
                                                                          dead})
                                                                , (/\dead ->
                                                                     traceError
                                                                       {bool}
                                                                       "Remaining asset is not decreasing") ]
                                                                {all dead.
                                                                   dead})
                                                         , (/\dead ->
                                                              traceError
                                                                {bool}
                                                                "Zero remaining assets not allowed") ]
                                                         {all dead. dead})
                                                  , (/\dead ->
                                                       traceError
                                                         {bool}
                                                         "Unlock not permitted until firstUnlockPossibleAfter time") ]
                                                  {all dead. dead})
                                           , (/\dead ->
                                                traceError
                                                  {bool}
                                                  "Missing beneficiary signature") ]
                                           {all dead. dead})))))
                  {all dead. dead}))
             [(/\dead -> traceError {unit} "PT5"), (/\dead -> ())]
             {all dead. dead})
      (/\dead ->
         let
           !x : Unit = trace {Unit} "Failed to parse ScriptContext" Unit
         in
         error {unit})
      {all dead. dead})
  (Constr 0
     [ Constr 0
         [ List []
         , List []
         , List []
         , I 0
         , Map []
         , List []
         , Map []
         , Constr 0
             [ Constr 0 [Constr 1 [I 110], Constr 1 []]
             , Constr 0 [Constr 1 [I 1100], Constr 1 []] ]
         , List [B #]
         , Map []
         , Map []
         , B #058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145
         , Map []
         , List []
         , Constr 1 []
         , Constr 1 [] ]
     , Constr 1 []
     , Constr 1
         [ Constr 0
             [ B #058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145
             , I 0 ]
         , Constr 0
             [ Constr 0
                 [ Constr 0 [Constr 0 [B #], Constr 1 []]
                 , Constr 0 [B #24, B #746573742d6173736574]
                 , I 1000
                 , I 0
                 , I 100
                 , I 10
                 , I 10 ] ] ] ])
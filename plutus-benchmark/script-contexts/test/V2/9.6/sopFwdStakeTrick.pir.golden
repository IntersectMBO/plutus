letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !go : list data -> List bytestring
    = \(xs : list data) ->
        case
          (List bytestring)
          xs
          [ (\(x : data) (xs : list data) ->
               Cons {bytestring} (unBData x) (go xs))
          , (Nil {bytestring}) ]
in
let
  !casePair : all a b r. pair a b -> (a -> b -> r) -> r
    = /\a b r -> \(p : pair a b) (f : a -> b -> r) -> case r p [f]
  data Credential | Credential_match where
    PubKeyCredential : bytestring -> Credential
    ScriptCredential : bytestring -> Credential
  !`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData` : data -> Credential
    = \(d : data) ->
        casePair
          {integer}
          {list data}
          {Credential}
          (unConstrData d)
          (\(index : integer) (args : list data) ->
             case
               (list data -> Credential)
               index
               [ (\(ds : list data) ->
                    PubKeyCredential (unBData (headList {data} ds)))
               , (\(ds : list data) ->
                    ScriptCredential (unBData (headList {data} ds))) ]
               args)
  data StakingCredential | StakingCredential_match where
    StakingHash : Credential -> StakingCredential
    StakingPtr : integer -> integer -> integer -> StakingCredential
  !`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData` :
     data -> StakingCredential
    = \(d : data) ->
        casePair
          {integer}
          {list data}
          {StakingCredential}
          (unConstrData d)
          (\(index : integer) (args : list data) ->
             case
               (list data -> StakingCredential)
               index
               [ (\(ds : list data) ->
                    StakingHash
                      (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                         (headList {data} ds)))
               , (\(ds : list data) ->
                    let
                      !l : list data = tailList {data} ds
                    in
                    StakingPtr
                      (unIData (headList {data} ds))
                      (unIData (headList {data} l))
                      (unIData (headList {data} (tailList {data} l)))) ]
               args)
  data DCert | DCert_match where
    DCertDelegDeRegKey : StakingCredential -> DCert
    DCertDelegDelegate : StakingCredential -> bytestring -> DCert
    DCertDelegRegKey : StakingCredential -> DCert
    DCertGenesis : DCert
    DCertMir : DCert
    DCertPoolRegister : bytestring -> bytestring -> DCert
    DCertPoolRetire : bytestring -> integer -> DCert
  !`$fUnsafeFromDataDCert_$cunsafeFromBuiltinData` :
     data -> DCert
    = \(d : data) ->
        casePair
          {integer}
          {list data}
          {DCert}
          (unConstrData d)
          (\(index : integer)
            (args : list data) ->
             case
               (list data -> DCert)
               index
               [ (\(ds : list data) ->
                    DCertDelegRegKey
                      (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                         (headList {data} ds)))
               , (\(ds : list data) ->
                    DCertDelegDeRegKey
                      (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                         (headList {data} ds)))
               , (\(ds : list data) ->
                    DCertDelegDelegate
                      (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                         (headList {data} ds))
                      (unBData (headList {data} (tailList {data} ds))))
               , (\(ds : list data) ->
                    DCertPoolRegister
                      (unBData (headList {data} ds))
                      (unBData (headList {data} (tailList {data} ds))))
               , (\(ds : list data) ->
                    DCertPoolRetire
                      (unBData (headList {data} ds))
                      (unIData (headList {data} (tailList {data} ds))))
               , (\(ds : list data) -> DCertGenesis)
               , (\(ds : list data) -> DCertMir) ]
               args)
in
letrec
  !go : list data -> List DCert
    = \(xs : list data) ->
        case
          (List DCert)
          xs
          [ (\(x : data) (xs : list data) ->
               Cons
                 {DCert}
                 (`$fUnsafeFromDataDCert_$cunsafeFromBuiltinData` x)
                 (go xs))
          , (Nil {DCert}) ]
in
let
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
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !`$fUnsafeFromDataMap_$cunsafeFromBuiltinData` :
     all k v.
       (\a -> data -> a) k ->
       (\a -> data -> a) v ->
       data ->
       (\k v -> List (Tuple2 k v)) k v
    = /\k v ->
        \(`$dUnsafeFromData` : (\a -> data -> a) k)
         (`$dUnsafeFromData` : (\a -> data -> a) v) ->
          letrec
            !go : list (pair data data) -> List (Tuple2 k v)
              = \(xs : list (pair data data)) ->
                  case
                    (List (Tuple2 k v))
                    xs
                    [ (\(tup : pair data data) (tups : list (pair data data)) ->
                         Cons
                           {Tuple2 k v}
                           (Tuple2
                              {k}
                              {v}
                              (`$dUnsafeFromData`
                                 (case
                                    data
                                    tup
                                    [(\(l : data) (r : data) -> l)]))
                              (`$dUnsafeFromData`
                                 (case
                                    data
                                    tup
                                    [(\(l : data) (r : data) -> r)])))
                           (go tups))
                    , (Nil {Tuple2 k v}) ]
          in
          \(d : data) -> go (unMapData d)
  ~`$fUnsafeFromDataValue` :
     data -> (\k v -> List (Tuple2 k v)) bytestring integer
    = `$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
        {bytestring}
        {integer}
        unBData
        unIData
  data Address | Address_match where
    Address : Credential -> Maybe StakingCredential -> Address
  data OutputDatum | OutputDatum_match where
    NoOutputDatum : OutputDatum
    OutputDatum : data -> OutputDatum
    OutputDatumHash : bytestring -> OutputDatum
  data TxOut | TxOut_match where
    TxOut :
      Address ->
      (\k v -> List (Tuple2 k v))
        bytestring
        ((\k v -> List (Tuple2 k v)) bytestring integer) ->
      OutputDatum ->
      Maybe bytestring ->
      TxOut
  !`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData` :
     data -> TxOut
    = \(eta : data) ->
        casePair
          {integer}
          {list data}
          {TxOut}
          (unConstrData eta)
          (\(index : integer)
            (args : list data) ->
             case
               (list data -> TxOut)
               index
               [ (\(ds : list data) ->
                    let
                      !l : list data = tailList {data} ds
                      !l : list data = tailList {data} l
                    in
                    TxOut
                      (let
                        !eta : data = headList {data} ds
                      in
                      casePair
                        {integer}
                        {list data}
                        {Address}
                        (unConstrData eta)
                        (\(index : integer)
                          (args : list data) ->
                           case
                             (list data -> Address)
                             index
                             [ (\(ds : list data) ->
                                  Address
                                    (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                       (headList {data} ds))
                                    (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                       {StakingCredential}
                                       `$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                       (headList
                                          {data}
                                          (tailList {data} ds)))) ]
                             args))
                      (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                         {bytestring}
                         {(\k v -> List (Tuple2 k v)) bytestring integer}
                         unBData
                         `$fUnsafeFromDataValue`
                         (headList {data} l))
                      (let
                        !d : data = headList {data} l
                      in
                      casePair
                        {integer}
                        {list data}
                        {OutputDatum}
                        (unConstrData d)
                        (\(index : integer) (args : list data) ->
                           case
                             (list data -> OutputDatum)
                             index
                             [ (\(ds : list data) -> NoOutputDatum)
                             , (\(ds : list data) ->
                                  OutputDatumHash
                                    (unBData (headList {data} ds)))
                             , (\(ds : list data) ->
                                  OutputDatum (headList {data} ds)) ]
                             args))
                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                         {bytestring}
                         unBData
                         (headList {data} (tailList {data} l)))) ]
               args)
in
letrec
  !go : list data -> List TxOut
    = \(xs : list data) ->
        case
          (List TxOut)
          xs
          [ (\(x : data) (xs : list data) ->
               Cons
                 {TxOut}
                 (`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData` x)
                 (go xs))
          , (Nil {TxOut}) ]
in
let
  !`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData` : data -> bytestring
    = \(d : data) ->
        casePair
          {integer}
          {list data}
          {bytestring}
          (unConstrData d)
          (\(index : integer) (args : list data) ->
             case
               (list data -> bytestring)
               index
               [(\(ds : list data) -> unBData (headList {data} ds))]
               args)
  data TxOutRef | TxOutRef_match where
    TxOutRef : bytestring -> integer -> TxOutRef
  !`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData` : data -> TxOutRef
    = \(d : data) ->
        casePair
          {integer}
          {list data}
          {TxOutRef}
          (unConstrData d)
          (\(index : integer) (args : list data) ->
             case
               (list data -> TxOutRef)
               index
               [ (\(ds : list data) ->
                    TxOutRef
                      (`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData`
                         (headList {data} ds))
                      (unIData (headList {data} (tailList {data} ds)))) ]
               args)
  data TxInInfo | TxInInfo_match where
    TxInInfo : TxOutRef -> TxOut -> TxInInfo
  !`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` : data -> TxInInfo
    = \(d : data) ->
        casePair
          {integer}
          {list data}
          {TxInInfo}
          (unConstrData d)
          (\(index : integer) (args : list data) ->
             case
               (list data -> TxInInfo)
               index
               [ (\(ds : list data) ->
                    TxInInfo
                      (`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData`
                         (headList {data} ds))
                      (`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData`
                         (headList {data} (tailList {data} ds)))) ]
               args)
in
letrec
  !go : list data -> List TxInInfo
    = \(xs : list data) ->
        case
          (List TxInInfo)
          xs
          [ (\(x : data) (xs : list data) ->
               Cons
                 {TxInInfo}
                 (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` x)
                 (go xs))
          , (Nil {TxInInfo}) ]
in
letrec
  !go : list data -> List TxInInfo
    = \(xs : list data) ->
        case
          (List TxInInfo)
          xs
          [ (\(x : data) (xs : list data) ->
               Cons
                 {TxInInfo}
                 (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` x)
                 (go xs))
          , (Nil {TxInInfo}) ]
in
let
  !`$fEqStakingCredential_$c==` : StakingCredential -> StakingCredential -> bool
    = \(ds : StakingCredential) (ds : StakingCredential) ->
        StakingCredential_match
          ds
          {bool}
          (\(l : Credential) ->
             StakingCredential_match
               ds
               {bool}
               (\(r : Credential) ->
                  Credential_match
                    l
                    {bool}
                    (\(l : bytestring) ->
                       Credential_match
                         r
                         {bool}
                         (\(r : bytestring) -> equalsByteString l r)
                         (\(ipv : bytestring) -> False))
                    (\(a : bytestring) ->
                       Credential_match
                         r
                         {bool}
                         (\(ipv : bytestring) -> False)
                         (\(a' : bytestring) -> equalsByteString a a')))
               (\(ipv : integer) (ipv : integer) (ipv : integer) -> False))
          (\(a : integer) (b : integer) (c : integer) ->
             StakingCredential_match
               ds
               {bool}
               (\(ipv : Credential) -> False)
               (\(a' : integer) (b' : integer) (c' : integer) ->
                  case
                    (all dead. bool)
                    (equalsInteger a a')
                    [ (/\dead -> False)
                    , (/\dead ->
                         case
                           (all dead. bool)
                           (equalsInteger b b')
                           [(/\dead -> False), (/\dead -> equalsInteger c c')]
                           {all dead. dead}) ]
                    {all dead. dead}))
  !`$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData` : data -> data
    = \(d : data) -> d
  !`$fUnsafeFromDataBool_$cunsafeFromBuiltinData` : data -> bool
    = \(d : data) ->
        casePair
          {integer}
          {list data}
          {bool}
          (unConstrData d)
          (\(index : integer) (args : list data) ->
             case
               (list data -> bool)
               index
               [(\(ds : list data) -> False), (\(ds : list data) -> True)]
               args)
  data (Extended :: * -> *) a | Extended_match where
    Finite : a -> Extended a
    NegInf : Extended a
    PosInf : Extended a
  !`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData` :
     all a. (\a -> data -> a) a -> data -> Extended a
    = /\a ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
          casePair
            {integer}
            {list data}
            {Extended a}
            (unConstrData d)
            (\(index : integer) (args : list data) ->
               case
                 (list data -> Extended a)
                 index
                 [ (\(ds : list data) -> NegInf {a})
                 , (\(ds : list data) ->
                      Finite {a} (`$dUnsafeFromData` (headList {data} ds)))
                 , (\(ds : list data) -> PosInf {a}) ]
                 args)
  data ScriptPurpose | ScriptPurpose_match where
    Certifying : DCert -> ScriptPurpose
    Minting : bytestring -> ScriptPurpose
    Rewarding : StakingCredential -> ScriptPurpose
    Spending : TxOutRef -> ScriptPurpose
  !`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` :
     data -> ScriptPurpose
    = \(d : data) ->
        casePair
          {integer}
          {list data}
          {ScriptPurpose}
          (unConstrData d)
          (\(index : integer)
            (args : list data) ->
             case
               (list data -> ScriptPurpose)
               index
               [ (\(ds : list data) -> Minting (unBData (headList {data} ds)))
               , (\(ds : list data) ->
                    Spending
                      (`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData`
                         (headList {data} ds)))
               , (\(ds : list data) ->
                    Rewarding
                      (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                         (headList {data} ds)))
               , (\(ds : list data) ->
                    Certifying
                      (`$fUnsafeFromDataDCert_$cunsafeFromBuiltinData`
                         (headList {data} ds))) ]
               args)
  data (LowerBound :: * -> *) a | LowerBound_match where
    LowerBound : Extended a -> bool -> LowerBound a
  data (UpperBound :: * -> *) a | UpperBound_match where
    UpperBound : Extended a -> bool -> UpperBound a
  data (Interval :: * -> *) a | Interval_match where
    Interval : LowerBound a -> UpperBound a -> Interval a
  data TxInfo | TxInfo_match where
    TxInfo :
      List TxInInfo ->
      List TxInInfo ->
      List TxOut ->
      (\k v -> List (Tuple2 k v))
        bytestring
        ((\k v -> List (Tuple2 k v)) bytestring integer) ->
      (\k v -> List (Tuple2 k v))
        bytestring
        ((\k v -> List (Tuple2 k v)) bytestring integer) ->
      List DCert ->
      (\k v -> List (Tuple2 k v)) StakingCredential integer ->
      Interval integer ->
      List bytestring ->
      (\k v -> List (Tuple2 k v)) ScriptPurpose data ->
      (\k v -> List (Tuple2 k v)) bytestring data ->
      bytestring ->
      TxInfo
  data ScriptContext | ScriptContext_match where
    ScriptContext : TxInfo -> ScriptPurpose -> ScriptContext
  data Unit | Unit_match where
    Unit : Unit
in
\(obsScriptCred : data)
 (ctx : data) ->
  ScriptContext_match
    (casePair
       {integer}
       {list data}
       {ScriptContext}
       (unConstrData ctx)
       (\(index : integer)
         (args : list data) ->
          case
            (list data -> ScriptContext)
            index
            [ (\(ds : list data) ->
                 ScriptContext
                   (let
                     !eta : data = headList {data} ds
                   in
                   casePair
                     {integer}
                     {list data}
                     {TxInfo}
                     (unConstrData eta)
                     (\(index : integer)
                       (args : list data) ->
                        case
                          (list data -> TxInfo)
                          index
                          [ (\(ds : list data) ->
                               let
                                 !l : list data = tailList {data} ds
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
                               TxInfo
                                 (let
                                   !d : data = headList {data} ds
                                 in
                                 go (unListData d))
                                 (let
                                   !d : data = headList {data} l
                                 in
                                 go (unListData d))
                                 (let
                                   !d : data = headList {data} l
                                 in
                                 go (unListData d))
                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                    {bytestring}
                                    {(\k v -> List (Tuple2 k v))
                                       bytestring
                                       integer}
                                    unBData
                                    `$fUnsafeFromDataValue`
                                    (headList {data} l))
                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                    {bytestring}
                                    {(\k v -> List (Tuple2 k v))
                                       bytestring
                                       integer}
                                    unBData
                                    `$fUnsafeFromDataValue`
                                    (headList {data} l))
                                 (let
                                   !d : data = headList {data} l
                                 in
                                 go (unListData d))
                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                    {StakingCredential}
                                    {integer}
                                    `$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                    unIData
                                    (headList {data} l))
                                 (let
                                   !d : data = headList {data} l
                                 in
                                 casePair
                                   {integer}
                                   {list data}
                                   {Interval integer}
                                   (unConstrData d)
                                   (\(index : integer)
                                     (args : list data) ->
                                      case
                                        (list data -> Interval integer)
                                        index
                                        [ (\(ds : list data) ->
                                             Interval
                                               {integer}
                                               (let
                                                 !d : data = headList {data} ds
                                               in
                                               casePair
                                                 {integer}
                                                 {list data}
                                                 {LowerBound integer}
                                                 (unConstrData d)
                                                 (\(index : integer)
                                                   (args : list data) ->
                                                    case
                                                      (list data ->
                                                       LowerBound integer)
                                                      index
                                                      [ (\(ds : list data) ->
                                                           LowerBound
                                                             {integer}
                                                             (`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData`
                                                                {integer}
                                                                unIData
                                                                (headList
                                                                   {data}
                                                                   ds))
                                                             (`$fUnsafeFromDataBool_$cunsafeFromBuiltinData`
                                                                (headList
                                                                   {data}
                                                                   (tailList
                                                                      {data}
                                                                      ds)))) ]
                                                      args))
                                               (let
                                                 !d : data
                                                   = headList
                                                       {data}
                                                       (tailList {data} ds)
                                               in
                                               casePair
                                                 {integer}
                                                 {list data}
                                                 {UpperBound integer}
                                                 (unConstrData d)
                                                 (\(index : integer)
                                                   (args : list data) ->
                                                    case
                                                      (list data ->
                                                       UpperBound integer)
                                                      index
                                                      [ (\(ds : list data) ->
                                                           UpperBound
                                                             {integer}
                                                             (`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData`
                                                                {integer}
                                                                unIData
                                                                (headList
                                                                   {data}
                                                                   ds))
                                                             (`$fUnsafeFromDataBool_$cunsafeFromBuiltinData`
                                                                (headList
                                                                   {data}
                                                                   (tailList
                                                                      {data}
                                                                      ds)))) ]
                                                      args))) ]
                                        args))
                                 (let
                                   !d : data = headList {data} l
                                 in
                                 go (unListData d))
                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                    {ScriptPurpose}
                                    {data}
                                    `$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                    `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                    (headList {data} l))
                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                    {bytestring}
                                    {data}
                                    unBData
                                    `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                    (headList {data} l))
                                 (`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData`
                                    (headList {data} (tailList {data} l)))) ]
                          args))
                   (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                      (headList {data} (tailList {data} ds)))) ]
            args))
    {Unit}
    (\(ds : TxInfo)
      (ds : ScriptPurpose) ->
       TxInfo_match
         ds
         {Unit}
         (\(ds : List TxInInfo)
           (ds : List TxInInfo)
           (ds : List TxOut)
           (ds :
              (\k v -> List (Tuple2 k v))
                bytestring
                ((\k v -> List (Tuple2 k v)) bytestring integer))
           (ds :
              (\k v -> List (Tuple2 k v))
                bytestring
                ((\k v -> List (Tuple2 k v)) bytestring integer))
           (ds : List DCert)
           (ds : (\k v -> List (Tuple2 k v)) StakingCredential integer) ->
            let
              !`$j` :
                 StakingCredential -> integer -> Unit
                = \(a : StakingCredential) ->
                    let
                      !`$j` :
                         StakingCredential -> integer -> Unit
                        = \(a : StakingCredential)
                           (ds : integer) ->
                            let
                              !obsScriptCred' :
                                 StakingCredential
                                = `$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                    obsScriptCred
                            in
                            letrec
                              !go :
                                 List (Tuple2 StakingCredential integer) -> Unit
                                = \(ds :
                                      List
                                        (Tuple2 StakingCredential integer)) ->
                                    List_match
                                      {Tuple2 StakingCredential integer}
                                      ds
                                      {all dead. Unit}
                                      (/\dead ->
                                         let
                                           !x : Unit
                                             = trace {Unit} "not found" Unit
                                         in
                                         error {Unit})
                                      (\(ds : Tuple2 StakingCredential integer)
                                        (xs' :
                                           List
                                             (Tuple2
                                                StakingCredential
                                                integer)) ->
                                         /\dead ->
                                           Tuple2_match
                                             {StakingCredential}
                                             {integer}
                                             ds
                                             {Unit}
                                             (\(c' : StakingCredential)
                                               (i : integer) ->
                                                case
                                                  (all dead. Unit)
                                                  (`$fEqStakingCredential_$c==`
                                                     c'
                                                     obsScriptCred')
                                                  [ (/\dead -> go xs')
                                                  , (/\dead -> Unit) ]
                                                  {all dead. dead}))
                                      {all dead. dead}
                            in
                            case
                              (all dead. Unit)
                              (`$fEqStakingCredential_$c==` obsScriptCred' a)
                              [ (/\dead ->
                                   case
                                     (all dead. Unit)
                                     (`$fEqStakingCredential_$c==`
                                        obsScriptCred'
                                        a)
                                     [(/\dead -> go ds), (/\dead -> Unit)]
                                     {all dead. dead})
                              , (/\dead -> Unit) ]
                              {all dead. dead}
                      !`$j` : List (Tuple2 StakingCredential integer) -> Unit
                        = \(rest : List (Tuple2 StakingCredential integer)) ->
                            List_match
                              {Tuple2 StakingCredential integer}
                              rest
                              {all dead. Unit}
                              (/\dead ->
                                 let
                                   !x : Unit = trace {Unit} "PT8" Unit
                                 in
                                 Tuple2_match
                                   {StakingCredential}
                                   {integer}
                                   (error {Tuple2 StakingCredential integer})
                                   {Unit}
                                   (\(a : StakingCredential) (ds : integer) ->
                                      `$j` a ds))
                              (\(x : Tuple2 StakingCredential integer)
                                (ds :
                                   List (Tuple2 StakingCredential integer)) ->
                                 /\dead ->
                                   Tuple2_match
                                     {StakingCredential}
                                     {integer}
                                     x
                                     {Unit}
                                     (\(a : StakingCredential) (ds : integer) ->
                                        `$j` a ds))
                              {all dead. dead}
                    in
                    \(ds : integer) ->
                      List_match
                        {Tuple2 StakingCredential integer}
                        ds
                        {all dead. Unit}
                        (/\dead ->
                           `$j`
                             (let
                               !x : Unit = trace {Unit} "PT9" Unit
                             in
                             error {List (Tuple2 StakingCredential integer)}))
                        (\(ds : Tuple2 StakingCredential integer)
                          (as : List (Tuple2 StakingCredential integer)) ->
                           /\dead -> `$j` as)
                        {all dead. dead}
            in
            \(ds : Interval integer)
             (ds : List bytestring)
             (ds : (\k v -> List (Tuple2 k v)) ScriptPurpose data)
             (ds : (\k v -> List (Tuple2 k v)) bytestring data)
             (ds : bytestring) ->
              List_match
                {Tuple2 StakingCredential integer}
                ds
                {all dead. Unit}
                (/\dead ->
                   let
                     !x : Unit = trace {Unit} "PT8" Unit
                   in
                   Tuple2_match
                     {StakingCredential}
                     {integer}
                     (error {Tuple2 StakingCredential integer})
                     {Unit}
                     (\(a : StakingCredential) (ds : integer) -> `$j` a ds))
                (\(x : Tuple2 StakingCredential integer)
                  (ds : List (Tuple2 StakingCredential integer)) ->
                   /\dead ->
                     Tuple2_match
                       {StakingCredential}
                       {integer}
                       x
                       {Unit}
                       (\(a : StakingCredential) (ds : integer) -> `$j` a ds))
                {all dead. dead}))
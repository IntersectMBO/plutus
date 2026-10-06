(let
    !`$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData` : data -> data
      = \(d : data) -> d
    data (Extended :: * -> *) a | Extended_match where
      Finite : a -> Extended a
      NegInf : Extended a
      PosInf : Extended a
    !`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData` :
       all a. (\a -> data -> a) a -> data -> Extended a
      = /\a ->
          \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
            case
              (Extended a)
              d
              [ (\(ds : list data) -> NegInf {a})
              , (\(ds : list data) ->
                   Finite {a} (`$dUnsafeFromData` (headList {data} ds)))
              , (\(ds : list data) -> PosInf {a}) ]
  in
  letrec
    data (List :: * -> *) a | List_match where
      Nil : List a
      Cons : a -> List a -> List a
  in
  let
    !`$fUnsafeFromDataList_$cunsafeFromBuiltinData` :
       all a. (\a -> data -> a) a -> data -> List a
      = /\a ->
          \(`$dUnsafeFromData` : (\a -> data -> a) a) ->
            letrec
              !go : list data -> List a
                = \(xs : list data) ->
                    case
                      (List a)
                      xs
                      [ (\(x : data) (xs : list data) ->
                           Cons {a} (`$dUnsafeFromData` x) (go xs))
                      , (Nil {a}) ]
            in
            \(d : data) -> go (unListData d)
    data Credential | Credential_match where
      PubKeyCredential : bytestring -> Credential
      ScriptCredential : bytestring -> Credential
    !`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData` : data -> Credential
      = \(d : data) ->
          case
            Credential
            d
            [ (\(ds : list data) ->
                 PubKeyCredential (unBData (headList {data} ds)))
            , (\(ds : list data) ->
                 ScriptCredential (unBData (headList {data} ds))) ]
    data StakingCredential | StakingCredential_match where
      StakingHash : Credential -> StakingCredential
      StakingPtr : integer -> integer -> integer -> StakingCredential
    !`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData` :
       data -> StakingCredential
      = \(d : data) ->
          case
            StakingCredential
            d
            [ (\(ds : list data) ->
                 StakingHash
                   (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                      (headList {data} ds)))
            , (\(ds : list data) ->
                 case
                   StakingCredential
                   ds
                   [ (\(ds : data) (ds : list data) ->
                        case
                          StakingCredential
                          ds
                          [ (\(ds : data) (ds : list data) ->
                               StakingPtr
                                 (unIData ds)
                                 (unIData ds)
                                 (unIData (headList {data} ds))) ]) ]) ]
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
          case
            DCert
            d
            [ (\(ds : list data) ->
                 DCertDelegRegKey
                   (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                      (headList {data} ds)))
            , (\(ds : list data) ->
                 DCertDelegDeRegKey
                   (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                      (headList {data} ds)))
            , (\(ds : list data) ->
                 case
                   DCert
                   ds
                   [ (\(ds : data)
                       (ds : list data) ->
                        DCertDelegDelegate
                          (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                             ds)
                          (unBData (headList {data} ds))) ])
            , (\(ds : list data) ->
                 case
                   DCert
                   ds
                   [ (\(ds : data) (ds : list data) ->
                        DCertPoolRegister
                          (unBData ds)
                          (unBData (headList {data} ds))) ])
            , (\(ds : list data) ->
                 case
                   DCert
                   ds
                   [ (\(ds : data) (ds : list data) ->
                        DCertPoolRetire
                          (unBData ds)
                          (unIData (headList {data} ds))) ])
            , (\(ds : list data) -> DCertGenesis)
            , (\(ds : list data) -> DCertMir) ]
    !`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData` : data -> bytestring
      = \(d : data) ->
          case
            bytestring
            d
            [(\(ds : list data) -> unBData (headList {data} ds))]
    data TxOutRef | TxOutRef_match where
      TxOutRef : bytestring -> integer -> TxOutRef
    !`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData` : data -> TxOutRef
      = \(d : data) ->
          case
            TxOutRef
            d
            [ (\(ds : list data) ->
                 case
                   TxOutRef
                   ds
                   [ (\(ds : data) (ds : list data) ->
                        TxOutRef
                          (`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData` ds)
                          (unIData (headList {data} ds))) ]) ]
    data ScriptPurpose | ScriptPurpose_match where
      Certifying : DCert -> ScriptPurpose
      Minting : bytestring -> ScriptPurpose
      Rewarding : StakingCredential -> ScriptPurpose
      Spending : TxOutRef -> ScriptPurpose
    !`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` :
       data -> ScriptPurpose
      = \(d : data) ->
          case
            ScriptPurpose
            d
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
    data (Maybe :: * -> *) a | Maybe_match where
      Just : a -> Maybe a
      Nothing : Maybe a
    !`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData` :
       all a. (\a -> data -> a) a -> data -> Maybe a
      = /\a ->
          \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
            case
              (Maybe a)
              d
              [ (\(ds : list data) ->
                   Just {a} (`$dUnsafeFromData` (headList {data} ds)))
              , (\(ds : list data) -> Nothing {a}) ]
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
                      [ (\(tup : pair data data)
                          (tups : list (pair data data)) ->
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
          case
            TxOut
            eta
            [ (\(ds : list data) ->
                 case
                   TxOut
                   ds
                   [ (\(ds : data)
                       (ds : list data) ->
                        case
                          TxOut
                          ds
                          [ (\(ds : data)
                              (ds : list data) ->
                               case
                                 TxOut
                                 ds
                                 [ (\(ds : data)
                                     (ds : list data) ->
                                      TxOut
                                        (case
                                           Address
                                           ds
                                           [ (\(ds : list data) ->
                                                case
                                                  Address
                                                  ds
                                                  [ (\(ds : data)
                                                      (ds : list data) ->
                                                       Address
                                                         (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                                            ds)
                                                         (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                            {StakingCredential}
                                                            `$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                            (headList
                                                               {data}
                                                               ds))) ]) ])
                                        (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                           {bytestring}
                                           {(\k v -> List (Tuple2 k v))
                                              bytestring
                                              integer}
                                           unBData
                                           `$fUnsafeFromDataValue`
                                           ds)
                                        (case
                                           OutputDatum
                                           ds
                                           [ (\(ds : list data) ->
                                                NoOutputDatum)
                                           , (\(ds : list data) ->
                                                OutputDatumHash
                                                  (unBData
                                                     (headList {data} ds)))
                                           , (\(ds : list data) ->
                                                OutputDatum
                                                  (headList {data} ds)) ])
                                        (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                           {bytestring}
                                           unBData
                                           (headList {data} ds))) ]) ]) ]) ]
    data TxInInfo | TxInInfo_match where
      TxInInfo : TxOutRef -> TxOut -> TxInInfo
    !`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` : data -> TxInInfo
      = \(d : data) ->
          case
            TxInInfo
            d
            [ (\(ds : list data) ->
                 case
                   TxInInfo
                   ds
                   [ (\(ds : data) (ds : list data) ->
                        TxInInfo
                          (`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData`
                             ds)
                          (`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData`
                             (headList {data} ds))) ]) ]
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
  in
  \(d : data) ->
    let
      !ds :
         ScriptContext
        = case
            ScriptContext
            d
            [ (\(ds : list data) ->
                 case
                   ScriptContext
                   ds
                   [ (\(ds : data)
                       (ds : list data) ->
                        ScriptContext
                          (case
                             TxInfo
                             ds
                             [ (\(ds : list data) ->
                                  case
                                    TxInfo
                                    ds
                                    [ (\(ds : data)
                                        (ds : list data) ->
                                         case
                                           TxInfo
                                           ds
                                           [ (\(ds : data)
                                               (ds : list data) ->
                                                case
                                                  TxInfo
                                                  ds
                                                  [ (\(ds : data)
                                                      (ds : list data) ->
                                                       case
                                                         TxInfo
                                                         ds
                                                         [ (\(ds : data)
                                                             (ds : list data) ->
                                                              case
                                                                TxInfo
                                                                ds
                                                                [ (\(ds : data)
                                                                    (ds :
                                                                       list
                                                                         data) ->
                                                                     case
                                                                       TxInfo
                                                                       ds
                                                                       [ (\(ds :
                                                                              data)
                                                                           (ds :
                                                                              list
                                                                                data) ->
                                                                            case
                                                                              TxInfo
                                                                              ds
                                                                              [ (\(ds :
                                                                                     data)
                                                                                  (ds :
                                                                                     list
                                                                                       data) ->
                                                                                   case
                                                                                     TxInfo
                                                                                     ds
                                                                                     [ (\(ds :
                                                                                            data)
                                                                                         (ds :
                                                                                            list
                                                                                              data) ->
                                                                                          case
                                                                                            TxInfo
                                                                                            ds
                                                                                            [ (\(ds :
                                                                                                   data)
                                                                                                (ds :
                                                                                                   list
                                                                                                     data) ->
                                                                                                 case
                                                                                                   TxInfo
                                                                                                   ds
                                                                                                   [ (\(ds :
                                                                                                          data)
                                                                                                       (ds :
                                                                                                          list
                                                                                                            data) ->
                                                                                                        case
                                                                                                          TxInfo
                                                                                                          ds
                                                                                                          [ (\(ds :
                                                                                                                 data)
                                                                                                              (ds :
                                                                                                                 list
                                                                                                                   data) ->
                                                                                                               TxInfo
                                                                                                                 (`$fUnsafeFromDataList_$cunsafeFromBuiltinData`
                                                                                                                    {TxInInfo}
                                                                                                                    `$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                                                                                    ds)
                                                                                                                 (`$fUnsafeFromDataList_$cunsafeFromBuiltinData`
                                                                                                                    {TxInInfo}
                                                                                                                    `$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                                                                                    ds)
                                                                                                                 (`$fUnsafeFromDataList_$cunsafeFromBuiltinData`
                                                                                                                    {TxOut}
                                                                                                                    `$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData`
                                                                                                                    ds)
                                                                                                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                                                                    {bytestring}
                                                                                                                    {(\k
                                                                                                                       v ->
                                                                                                                        List
                                                                                                                          (Tuple2
                                                                                                                             k
                                                                                                                             v))
                                                                                                                       bytestring
                                                                                                                       integer}
                                                                                                                    unBData
                                                                                                                    `$fUnsafeFromDataValue`
                                                                                                                    ds)
                                                                                                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                                                                    {bytestring}
                                                                                                                    {(\k
                                                                                                                       v ->
                                                                                                                        List
                                                                                                                          (Tuple2
                                                                                                                             k
                                                                                                                             v))
                                                                                                                       bytestring
                                                                                                                       integer}
                                                                                                                    unBData
                                                                                                                    `$fUnsafeFromDataValue`
                                                                                                                    ds)
                                                                                                                 (`$fUnsafeFromDataList_$cunsafeFromBuiltinData`
                                                                                                                    {DCert}
                                                                                                                    `$fUnsafeFromDataDCert_$cunsafeFromBuiltinData`
                                                                                                                    ds)
                                                                                                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                                                                    {StakingCredential}
                                                                                                                    {integer}
                                                                                                                    `$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                                                                                    unIData
                                                                                                                    ds)
                                                                                                                 (case
                                                                                                                    (Interval
                                                                                                                       integer)
                                                                                                                    ds
                                                                                                                    [ (\(ds :
                                                                                                                           list
                                                                                                                             data) ->
                                                                                                                         case
                                                                                                                           (Interval
                                                                                                                              integer)
                                                                                                                           ds
                                                                                                                           [ (\(ds :
                                                                                                                                  data)
                                                                                                                               (ds :
                                                                                                                                  list
                                                                                                                                    data) ->
                                                                                                                                Interval
                                                                                                                                  {integer}
                                                                                                                                  (case
                                                                                                                                     (LowerBound
                                                                                                                                        integer)
                                                                                                                                     ds
                                                                                                                                     [ (\(ds :
                                                                                                                                            list
                                                                                                                                              data) ->
                                                                                                                                          case
                                                                                                                                            (LowerBound
                                                                                                                                               integer)
                                                                                                                                            ds
                                                                                                                                            [ (\(ds :
                                                                                                                                                   data)
                                                                                                                                                (ds :
                                                                                                                                                   list
                                                                                                                                                     data) ->
                                                                                                                                                 LowerBound
                                                                                                                                                   {integer}
                                                                                                                                                   (`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData`
                                                                                                                                                      {integer}
                                                                                                                                                      unIData
                                                                                                                                                      ds)
                                                                                                                                                   (case
                                                                                                                                                      bool
                                                                                                                                                      (headList
                                                                                                                                                         {data}
                                                                                                                                                         ds)
                                                                                                                                                      [ (\(ds :
                                                                                                                                                             list
                                                                                                                                                               data) ->
                                                                                                                                                           False)
                                                                                                                                                      , (\(ds :
                                                                                                                                                             list
                                                                                                                                                               data) ->
                                                                                                                                                           True) ])) ]) ])
                                                                                                                                  (case
                                                                                                                                     (UpperBound
                                                                                                                                        integer)
                                                                                                                                     (headList
                                                                                                                                        {data}
                                                                                                                                        ds)
                                                                                                                                     [ (\(ds :
                                                                                                                                            list
                                                                                                                                              data) ->
                                                                                                                                          case
                                                                                                                                            (UpperBound
                                                                                                                                               integer)
                                                                                                                                            ds
                                                                                                                                            [ (\(ds :
                                                                                                                                                   data)
                                                                                                                                                (ds :
                                                                                                                                                   list
                                                                                                                                                     data) ->
                                                                                                                                                 UpperBound
                                                                                                                                                   {integer}
                                                                                                                                                   (`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData`
                                                                                                                                                      {integer}
                                                                                                                                                      unIData
                                                                                                                                                      ds)
                                                                                                                                                   (case
                                                                                                                                                      bool
                                                                                                                                                      (headList
                                                                                                                                                         {data}
                                                                                                                                                         ds)
                                                                                                                                                      [ (\(ds :
                                                                                                                                                             list
                                                                                                                                                               data) ->
                                                                                                                                                           False)
                                                                                                                                                      , (\(ds :
                                                                                                                                                             list
                                                                                                                                                               data) ->
                                                                                                                                                           True) ])) ]) ])) ]) ])
                                                                                                                 (`$fUnsafeFromDataList_$cunsafeFromBuiltinData`
                                                                                                                    {bytestring}
                                                                                                                    unBData
                                                                                                                    ds)
                                                                                                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                                                                    {ScriptPurpose}
                                                                                                                    {data}
                                                                                                                    `$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                                                                                    `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                                    ds)
                                                                                                                 (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                                                                    {bytestring}
                                                                                                                    {data}
                                                                                                                    unBData
                                                                                                                    `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                                    ds)
                                                                                                                 (`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData`
                                                                                                                    (headList
                                                                                                                       {data}
                                                                                                                       ds))) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ])
                          (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                             (headList {data} ds))) ]) ]
    in
    ())
  (Constr 0
     [ Constr 0
         [ List []
         , List []
         , List
             [ Constr 0
                 [ Constr 0 [Constr 0 [B #], Constr 1 []]
                 , Map [(B #, Map [(B #, I 1)])]
                 , Constr 0 []
                 , Constr 1 [] ] ]
         , Map []
         , Map []
         , List []
         , Map []
         , Constr 0
             [ Constr 0 [Constr 0 [], Constr 1 []]
             , Constr 0 [Constr 2 [], Constr 1 []] ]
         , List []
         , Map []
         , Map []
         , Constr 0 [B #] ]
     , Constr 1 [Constr 0 [Constr 0 [B #], I 0]] ])
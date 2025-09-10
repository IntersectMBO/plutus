(let
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
  in
  letrec
    data (List :: * -> *) a | List_match where
      Nil : List a
      Cons : a -> List a -> List a
  in
  letrec
    !go : list data -> List Credential
      = \(xs : list data) ->
          case
            (List Credential)
            xs
            [ (\(x : data) (xs : list data) ->
                 Cons
                   {Credential}
                   (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData` x)
                   (go xs))
            , (Nil {Credential}) ]
  in
  let
    data GovernanceActionId | GovernanceActionId_match where
      GovernanceActionId : bytestring -> integer -> GovernanceActionId
    !`$fUnsafeFromDataGovernanceAction_$cunsafeFromBuiltinData` :
       data -> GovernanceActionId
      = \(d : data) ->
          casePair
            {integer}
            {list data}
            {GovernanceActionId}
            (unConstrData d)
            (\(index : integer) (args : list data) ->
               case
                 (list data -> GovernanceActionId)
                 index
                 [ (\(ds : list data) ->
                      GovernanceActionId
                        (unBData (headList {data} ds))
                        (unIData (headList {data} (tailList {data} ds)))) ]
                 args)
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
    data ProtocolVersion | ProtocolVersion_match where
      ProtocolVersion : integer -> integer -> ProtocolVersion
    data Rational | Rational_match where
      Rational : integer -> integer -> Rational
    data GovernanceAction | GovernanceAction_match where
      HardForkInitiation :
        Maybe GovernanceActionId -> ProtocolVersion -> GovernanceAction
      InfoAction : GovernanceAction
      NewConstitution :
        Maybe GovernanceActionId -> Maybe bytestring -> GovernanceAction
      NoConfidence : Maybe GovernanceActionId -> GovernanceAction
      ParameterChange :
        Maybe GovernanceActionId -> data -> Maybe bytestring -> GovernanceAction
      TreasuryWithdrawals :
        (\k v -> List (Tuple2 k v)) Credential integer ->
        Maybe bytestring ->
        GovernanceAction
      UpdateCommittee :
        Maybe GovernanceActionId ->
        List Credential ->
        (\k v -> List (Tuple2 k v)) Credential integer ->
        Rational ->
        GovernanceAction
    data ProposalProcedure | ProposalProcedure_match where
      ProposalProcedure :
        integer -> Credential -> GovernanceAction -> ProposalProcedure
  in
  letrec
    !euclid : integer -> integer -> integer
      = \(x : integer) (y : integer) ->
          case
            (all dead. integer)
            (equalsInteger 0 y)
            [(/\dead -> euclid y (modInteger x y)), (/\dead -> x)]
            {all dead. dead}
  in
  let
    data Unit | Unit_match where
      Unit : Unit
  in
  letrec
    !unsafeRatio : integer -> integer -> Rational
      = \(n : integer) (d : integer) ->
          case
            (all dead. Rational)
            (equalsInteger 0 d)
            [ (/\dead ->
                 case
                   (all dead. Rational)
                   (lessThanInteger d 0)
                   [ (/\dead ->
                        let
                          !gcd' : integer = euclid n d
                        in
                        Rational
                          (quotientInteger n gcd')
                          (quotientInteger d gcd'))
                   , (/\dead ->
                        unsafeRatio
                          (subtractInteger 0 n)
                          (subtractInteger 0 d)) ]
                   {all dead. dead})
            , (/\dead ->
                 let
                   !x : Unit = trace {Unit} "PT3" Unit
                 in
                 error {Rational}) ]
            {all dead. dead}
  in
  let
    !`$fUnsafeFromDataProposalProcedure_$cunsafeFromBuiltinData` :
       data -> ProposalProcedure
      = \(d : data) ->
          casePair
            {integer}
            {list data}
            {ProposalProcedure}
            (unConstrData d)
            (\(index : integer)
              (args : list data) ->
               case
                 (list data -> ProposalProcedure)
                 index
                 [ (\(ds : list data) ->
                      let
                        !l : list data = tailList {data} ds
                      in
                      ProposalProcedure
                        (unIData (headList {data} ds))
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} l))
                        (let
                          !eta : data = headList {data} (tailList {data} l)
                        in
                        casePair
                          {integer}
                          {list data}
                          {GovernanceAction}
                          (unConstrData eta)
                          (\(index : integer)
                            (args : list data) ->
                             case
                               (list data -> GovernanceAction)
                               index
                               [ (\(ds : list data) ->
                                    let
                                      !l : list data = tailList {data} ds
                                    in
                                    ParameterChange
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {GovernanceActionId}
                                         `$fUnsafeFromDataGovernanceAction_$cunsafeFromBuiltinData`
                                         (headList {data} ds))
                                      (headList {data} l)
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {bytestring}
                                         unBData
                                         (headList {data} (tailList {data} l))))
                               , (\(ds : list data) ->
                                    HardForkInitiation
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {GovernanceActionId}
                                         `$fUnsafeFromDataGovernanceAction_$cunsafeFromBuiltinData`
                                         (headList {data} ds))
                                      (let
                                        !d : data
                                          = headList {data} (tailList {data} ds)
                                      in
                                      casePair
                                        {integer}
                                        {list data}
                                        {ProtocolVersion}
                                        (unConstrData d)
                                        (\(index : integer)
                                          (args : list data) ->
                                           case
                                             (list data -> ProtocolVersion)
                                             index
                                             [ (\(ds : list data) ->
                                                  ProtocolVersion
                                                    (unIData
                                                       (headList {data} ds))
                                                    (unIData
                                                       (headList
                                                          {data}
                                                          (tailList
                                                             {data}
                                                             ds)))) ]
                                             args)))
                               , (\(ds : list data) ->
                                    TreasuryWithdrawals
                                      (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                         {Credential}
                                         {integer}
                                         `$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                         unIData
                                         (headList {data} ds))
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {bytestring}
                                         unBData
                                         (headList
                                            {data}
                                            (tailList {data} ds))))
                               , (\(ds : list data) ->
                                    NoConfidence
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {GovernanceActionId}
                                         `$fUnsafeFromDataGovernanceAction_$cunsafeFromBuiltinData`
                                         (headList {data} ds)))
                               , (\(ds : list data) ->
                                    let
                                      !l : list data = tailList {data} ds
                                      !l : list data = tailList {data} l
                                    in
                                    UpdateCommittee
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {GovernanceActionId}
                                         `$fUnsafeFromDataGovernanceAction_$cunsafeFromBuiltinData`
                                         (headList {data} ds))
                                      (let
                                        !d : data = headList {data} l
                                      in
                                      go (unListData d))
                                      (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                         {Credential}
                                         {integer}
                                         `$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                         unIData
                                         (headList {data} l))
                                      (let
                                        !x : data
                                          = headList {data} (tailList {data} l)
                                      in
                                      Tuple2_match
                                        {integer}
                                        {integer}
                                        (casePair
                                           {integer}
                                           {list data}
                                           {Tuple2 integer integer}
                                           (unConstrData x)
                                           (\(index : integer)
                                             (args : list data) ->
                                              case
                                                (list data ->
                                                 Tuple2 integer integer)
                                                index
                                                [ (\(ds : list data) ->
                                                     Tuple2
                                                       {integer}
                                                       {integer}
                                                       (unIData
                                                          (headList {data} ds))
                                                       (unIData
                                                          (headList
                                                             {data}
                                                             (tailList
                                                                {data}
                                                                ds)))) ]
                                                args))
                                        {Rational}
                                        (\(a : integer) (b : integer) ->
                                           unsafeRatio a b)))
                               , (\(ds : list data) ->
                                    NewConstitution
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {GovernanceActionId}
                                         `$fUnsafeFromDataGovernanceAction_$cunsafeFromBuiltinData`
                                         (headList {data} ds))
                                      (let
                                        !eta : data
                                          = headList {data} (tailList {data} ds)
                                      in
                                      casePair
                                        {integer}
                                        {list data}
                                        {Maybe bytestring}
                                        (unConstrData eta)
                                        (\(index : integer)
                                          (args : list data) ->
                                           case
                                             (list data -> Maybe bytestring)
                                             index
                                             [ (\(ds : list data) ->
                                                  `$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                    {bytestring}
                                                    unBData
                                                    (headList {data} ds)) ]
                                             args)))
                               , (\(ds : list data) -> InfoAction) ]
                               args))) ]
                 args)
  in
  letrec
    !go : list data -> List ProposalProcedure
      = \(xs : list data) ->
          case
            (List ProposalProcedure)
            xs
            [ (\(x : data) (xs : list data) ->
                 Cons
                   {ProposalProcedure}
                   (`$fUnsafeFromDataProposalProcedure_$cunsafeFromBuiltinData`
                      x)
                   (go xs))
            , (Nil {ProposalProcedure}) ]
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
    data DRep | DRep_match where
      DRep : Credential -> DRep
      DRepAlwaysAbstain : DRep
      DRepAlwaysNoConfidence : DRep
    !`$fUnsafeFromDataDRep_$cunsafeFromBuiltinData` : data -> DRep
      = \(d : data) ->
          casePair
            {integer}
            {list data}
            {DRep}
            (unConstrData d)
            (\(index : integer) (args : list data) ->
               case
                 (list data -> DRep)
                 index
                 [ (\(ds : list data) ->
                      DRep
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds)))
                 , (\(ds : list data) -> DRepAlwaysAbstain)
                 , (\(ds : list data) -> DRepAlwaysNoConfidence) ]
                 args)
    data Delegatee | Delegatee_match where
      DelegStake : bytestring -> Delegatee
      DelegStakeVote : bytestring -> DRep -> Delegatee
      DelegVote : DRep -> Delegatee
    !`$fUnsafeFromDataDelegatee_$cunsafeFromBuiltinData` : data -> Delegatee
      = \(d : data) ->
          casePair
            {integer}
            {list data}
            {Delegatee}
            (unConstrData d)
            (\(index : integer) (args : list data) ->
               case
                 (list data -> Delegatee)
                 index
                 [ (\(ds : list data) ->
                      DelegStake (unBData (headList {data} ds)))
                 , (\(ds : list data) ->
                      DelegVote
                        (`$fUnsafeFromDataDRep_$cunsafeFromBuiltinData`
                           (headList {data} ds)))
                 , (\(ds : list data) ->
                      DelegStakeVote
                        (unBData (headList {data} ds))
                        (`$fUnsafeFromDataDRep_$cunsafeFromBuiltinData`
                           (headList {data} (tailList {data} ds)))) ]
                 args)
    data TxCert | TxCert_match where
      TxCertAuthHotCommittee : Credential -> Credential -> TxCert
      TxCertDelegStaking : Credential -> Delegatee -> TxCert
      TxCertPoolRegister : bytestring -> bytestring -> TxCert
      TxCertPoolRetire : bytestring -> integer -> TxCert
      TxCertRegDRep : Credential -> integer -> TxCert
      TxCertRegDeleg : Credential -> Delegatee -> integer -> TxCert
      TxCertRegStaking : Credential -> Maybe integer -> TxCert
      TxCertResignColdCommittee : Credential -> TxCert
      TxCertUnRegDRep : Credential -> integer -> TxCert
      TxCertUnRegStaking : Credential -> Maybe integer -> TxCert
      TxCertUpdateDRep : Credential -> TxCert
    !`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` : data -> TxCert
      = \(eta : data) ->
          casePair
            {integer}
            {list data}
            {TxCert}
            (unConstrData eta)
            (\(index : integer) (args : list data) ->
               case
                 (list data -> TxCert)
                 index
                 [ (\(ds : list data) ->
                      TxCertRegStaking
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds))
                        (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                           {integer}
                           unIData
                           (headList {data} (tailList {data} ds))))
                 , (\(ds : list data) ->
                      TxCertUnRegStaking
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds))
                        (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                           {integer}
                           unIData
                           (headList {data} (tailList {data} ds))))
                 , (\(ds : list data) ->
                      TxCertDelegStaking
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds))
                        (`$fUnsafeFromDataDelegatee_$cunsafeFromBuiltinData`
                           (headList {data} (tailList {data} ds))))
                 , (\(ds : list data) ->
                      let
                        !l : list data = tailList {data} ds
                      in
                      TxCertRegDeleg
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds))
                        (`$fUnsafeFromDataDelegatee_$cunsafeFromBuiltinData`
                           (headList {data} l))
                        (unIData (headList {data} (tailList {data} l))))
                 , (\(ds : list data) ->
                      TxCertRegDRep
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds))
                        (unIData (headList {data} (tailList {data} ds))))
                 , (\(ds : list data) ->
                      TxCertUpdateDRep
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds)))
                 , (\(ds : list data) ->
                      TxCertUnRegDRep
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds))
                        (unIData (headList {data} (tailList {data} ds))))
                 , (\(ds : list data) ->
                      TxCertPoolRegister
                        (unBData (headList {data} ds))
                        (unBData (headList {data} (tailList {data} ds))))
                 , (\(ds : list data) ->
                      TxCertPoolRetire
                        (unBData (headList {data} ds))
                        (unIData (headList {data} (tailList {data} ds))))
                 , (\(ds : list data) ->
                      TxCertAuthHotCommittee
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds))
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} (tailList {data} ds))))
                 , (\(ds : list data) ->
                      TxCertResignColdCommittee
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds))) ]
                 args)
  in
  letrec
    !go : list data -> List TxCert
      = \(xs : list data) ->
          case
            (List TxCert)
            xs
            [ (\(x : data) (xs : list data) ->
                 Cons
                   {TxCert}
                   (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` x)
                   (go xs))
            , (Nil {TxCert}) ]
  in
  let
    data StakingCredential | StakingCredential_match where
      StakingHash : Credential -> StakingCredential
      StakingPtr : integer -> integer -> integer -> StakingCredential
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
                                         (\(d : data) ->
                                            casePair
                                              {integer}
                                              {list data}
                                              {StakingCredential}
                                              (unConstrData d)
                                              (\(index : integer)
                                                (args : list data) ->
                                                 case
                                                   (list data ->
                                                    StakingCredential)
                                                   index
                                                   [ (\(ds : list data) ->
                                                        StakingHash
                                                          (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                                             (headList
                                                                {data}
                                                                ds)))
                                                   , (\(ds : list data) ->
                                                        let
                                                          !l : list data
                                                            = tailList {data} ds
                                                        in
                                                        StakingPtr
                                                          (unIData
                                                             (headList
                                                                {data}
                                                                ds))
                                                          (unIData
                                                             (headList
                                                                {data}
                                                                l))
                                                          (unIData
                                                             (headList
                                                                {data}
                                                                (tailList
                                                                   {data}
                                                                   l)))) ]
                                                   args))
                                         (headList
                                            {data}
                                            (tailList {data} ds)))) ]
                               args))
                        (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                           {bytestring}
                           {(\k v -> List (Tuple2 k v)) bytestring integer}
                           unBData
                           (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                              {bytestring}
                              {integer}
                              unBData
                              unIData)
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
                        (unBData (headList {data} ds))
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
    data Voter | Voter_match where
      CommitteeVoter : Credential -> Voter
      DRepVoter : Credential -> Voter
      StakePoolVoter : bytestring -> Voter
    !`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` : data -> Voter
      = \(d : data) ->
          casePair
            {integer}
            {list data}
            {Voter}
            (unConstrData d)
            (\(index : integer) (args : list data) ->
               case
                 (list data -> Voter)
                 index
                 [ (\(ds : list data) ->
                      CommitteeVoter
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds)))
                 , (\(ds : list data) ->
                      DRepVoter
                        (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                           (headList {data} ds)))
                 , (\(ds : list data) ->
                      StakePoolVoter (unBData (headList {data} ds))) ]
                 args)
    data ScriptInfo | ScriptInfo_match where
      CertifyingScript : integer -> TxCert -> ScriptInfo
      MintingScript : bytestring -> ScriptInfo
      ProposingScript : integer -> ProposalProcedure -> ScriptInfo
      RewardingScript : Credential -> ScriptInfo
      SpendingScript : TxOutRef -> Maybe data -> ScriptInfo
      VotingScript : Voter -> ScriptInfo
    data (LowerBound :: * -> *) a | LowerBound_match where
      LowerBound : Extended a -> bool -> LowerBound a
    data (UpperBound :: * -> *) a | UpperBound_match where
      UpperBound : Extended a -> bool -> UpperBound a
    data (Interval :: * -> *) a | Interval_match where
      Interval : LowerBound a -> UpperBound a -> Interval a
    data ScriptPurpose | ScriptPurpose_match where
      Certifying : integer -> TxCert -> ScriptPurpose
      Minting : bytestring -> ScriptPurpose
      Proposing : integer -> ProposalProcedure -> ScriptPurpose
      Rewarding : Credential -> ScriptPurpose
      Spending : TxOutRef -> ScriptPurpose
      Voting : Voter -> ScriptPurpose
    data Vote | Vote_match where
      Abstain : Vote
      VoteNo : Vote
      VoteYes : Vote
    data TxInfo | TxInfo_match where
      TxInfo :
        List TxInInfo ->
        List TxInInfo ->
        List TxOut ->
        integer ->
        (\k v -> List (Tuple2 k v))
          bytestring
          ((\k v -> List (Tuple2 k v)) bytestring integer) ->
        List TxCert ->
        (\k v -> List (Tuple2 k v)) Credential integer ->
        Interval integer ->
        List bytestring ->
        (\k v -> List (Tuple2 k v)) ScriptPurpose data ->
        (\k v -> List (Tuple2 k v)) bytestring data ->
        bytestring ->
        (\k v -> List (Tuple2 k v))
          Voter
          ((\k v -> List (Tuple2 k v)) GovernanceActionId Vote) ->
        List ProposalProcedure ->
        Maybe integer ->
        Maybe integer ->
        TxInfo
    data ScriptContext | ScriptContext_match where
      ScriptContext : TxInfo -> data -> ScriptInfo -> ScriptContext
  in
  \(d : data) ->
    let
      !ds :
         ScriptContext
        = casePair
            {integer}
            {list data}
            {ScriptContext}
            (unConstrData d)
            (\(index : integer)
              (args : list data) ->
               case
                 (list data -> ScriptContext)
                 index
                 [ (\(ds : list data) ->
                      let
                        !l : list data = tailList {data} ds
                      in
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
                                      (unIData (headList {data} l))
                                      (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                         {bytestring}
                                         {(\k v -> List (Tuple2 k v))
                                            bytestring
                                            integer}
                                         unBData
                                         (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                            {bytestring}
                                            {integer}
                                            unBData
                                            unIData)
                                         (headList {data} l))
                                      (let
                                        !d : data = headList {data} l
                                      in
                                      go (unListData d))
                                      (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                         {Credential}
                                         {integer}
                                         `$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
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
                                                      !d : data
                                                        = headList {data} ds
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
                                                           [ (\(ds :
                                                                  list data) ->
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
                                                           [ (\(ds :
                                                                  list data) ->
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
                                         (\(d : data) ->
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
                                                   [ (\(ds : list data) ->
                                                        Minting
                                                          (unBData
                                                             (headList
                                                                {data}
                                                                ds)))
                                                   , (\(ds : list data) ->
                                                        Spending
                                                          (`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData`
                                                             (headList
                                                                {data}
                                                                ds)))
                                                   , (\(ds : list data) ->
                                                        Rewarding
                                                          (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                                             (headList
                                                                {data}
                                                                ds)))
                                                   , (\(ds : list data) ->
                                                        Certifying
                                                          (unIData
                                                             (headList
                                                                {data}
                                                                ds))
                                                          (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                             (headList
                                                                {data}
                                                                (tailList
                                                                   {data}
                                                                   ds))))
                                                   , (\(ds : list data) ->
                                                        Voting
                                                          (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                             (headList
                                                                {data}
                                                                ds)))
                                                   , (\(ds : list data) ->
                                                        Proposing
                                                          (unIData
                                                             (headList
                                                                {data}
                                                                ds))
                                                          (`$fUnsafeFromDataProposalProcedure_$cunsafeFromBuiltinData`
                                                             (headList
                                                                {data}
                                                                (tailList
                                                                   {data}
                                                                   ds)))) ]
                                                   args))
                                         `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                         (headList {data} l))
                                      (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                         {bytestring}
                                         {data}
                                         unBData
                                         `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                         (headList {data} l))
                                      (unBData (headList {data} l))
                                      (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                         {Voter}
                                         {(\k v -> List (Tuple2 k v))
                                            GovernanceActionId
                                            Vote}
                                         `$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                         (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                            {GovernanceActionId}
                                            {Vote}
                                            `$fUnsafeFromDataGovernanceAction_$cunsafeFromBuiltinData`
                                            (\(d : data) ->
                                               casePair
                                                 {integer}
                                                 {list data}
                                                 {Vote}
                                                 (unConstrData d)
                                                 (\(index : integer)
                                                   (args : list data) ->
                                                    case
                                                      (list data -> Vote)
                                                      index
                                                      [ (\(ds : list data) ->
                                                           VoteNo)
                                                      , (\(ds : list data) ->
                                                           VoteYes)
                                                      , (\(ds : list data) ->
                                                           Abstain) ]
                                                      args)))
                                         (headList {data} l))
                                      (let
                                        !d : data = headList {data} l
                                      in
                                      go (unListData d))
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {integer}
                                         unIData
                                         (headList {data} l))
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {integer}
                                         unIData
                                         (headList
                                            {data}
                                            (tailList {data} l)))) ]
                               args))
                        (headList {data} l)
                        (let
                          !eta : data = headList {data} (tailList {data} l)
                        in
                        casePair
                          {integer}
                          {list data}
                          {ScriptInfo}
                          (unConstrData eta)
                          (\(index : integer)
                            (args : list data) ->
                             case
                               (list data -> ScriptInfo)
                               index
                               [ (\(ds : list data) ->
                                    MintingScript
                                      (unBData (headList {data} ds)))
                               , (\(ds : list data) ->
                                    SpendingScript
                                      (`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData`
                                         (headList {data} ds))
                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                         {data}
                                         `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                         (headList
                                            {data}
                                            (tailList {data} ds))))
                               , (\(ds : list data) ->
                                    RewardingScript
                                      (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                         (headList {data} ds)))
                               , (\(ds : list data) ->
                                    CertifyingScript
                                      (unIData (headList {data} ds))
                                      (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                         (headList
                                            {data}
                                            (tailList {data} ds))))
                               , (\(ds : list data) ->
                                    VotingScript
                                      (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                         (headList {data} ds)))
                               , (\(ds : list data) ->
                                    ProposingScript
                                      (unIData (headList {data} ds))
                                      (`$fUnsafeFromDataProposalProcedure_$cunsafeFromBuiltinData`
                                         (headList
                                            {data}
                                            (tailList {data} ds)))) ]
                               args))) ]
                 args)
    in
    Unit)
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
         , I 10000
         , Map []
         , List []
         , Map []
         , Constr 0
             [ Constr 0 [Constr 0 [], Constr 1 []]
             , Constr 0 [Constr 2 [], Constr 1 []] ]
         , List []
         , Map []
         , Map []
         , B #
         , Map []
         , List []
         , Constr 1 []
         , Constr 1 [] ]
     , I 1
     , Constr 1 [Constr 0 [B #, I 0], Constr 1 []] ])
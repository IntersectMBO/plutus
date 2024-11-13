{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DerivingVia   #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module PlutusLedgerApi.Test.Orphans.V3.Contexts () where

import Control.Monad (guard)
import Data.Coerce (coerce)
import Data.Set qualified as Set
import PlutusLedgerApi.Test.Orphans.PlutusTx (Blake2b256Hash (Blake2b256Hash))
import PlutusLedgerApi.Test.Orphans.V1.Interval ()
import PlutusLedgerApi.Test.Orphans.V2.Tx ()
import PlutusLedgerApi.Test.Orphans.V3.MintValue ()
import PlutusLedgerApi.V1.Credential (Credential)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.Scripts (Datum, DatumHash, Redeemer, ScriptHash)
import PlutusLedgerApi.V1.Time (POSIXTimeRange)
import PlutusLedgerApi.V1.Value (CurrencySymbol, Lovelace)
import PlutusLedgerApi.V2.Tx (TxOut)
import PlutusLedgerApi.V3.Contexts (ChangedParameters (ChangedParameters),
                                    ColdCommitteeCredential (ColdCommitteeCredential),
                                    Committee (Committee), Constitution (Constitution),
                                    DRep (DRep, DRepAlwaysAbstain, DRepAlwaysNoConfidence),
                                    DRepCredential (DRepCredential),
                                    Delegatee (DelegStake, DelegStakeVote, DelegVote),
                                    GovernanceAction (..), GovernanceActionId (GovernanceActionId),
                                    HotCommitteeCredential (HotCommitteeCredential),
                                    ProposalProcedure (ProposalProcedure),
                                    ProtocolVersion (ProtocolVersion),
                                    ScriptContext (ScriptContext), ScriptInfo (..),
                                    ScriptPurpose (..), TxCert (..), TxInInfo (TxInInfo),
                                    TxInfo (TxInfo), Vote (Abstain, VoteNo, VoteYes),
                                    Voter (CommitteeVoter, DRepVoter, StakePoolVoter))
import PlutusLedgerApi.V3.MintValue (MintValue)
import PlutusLedgerApi.V3.Tx (TxId (TxId), TxOutRef (TxOutRef))
import PlutusTx.AssocMap (Map)
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Ratio qualified as Ratio
import Test.QuickCheck (Arbitrary (arbitrary, shrink), Arbitrary1 (liftArbitrary, liftShrink),
                        CoArbitrary (coarbitrary), Function (function), NonEmptyList (NonEmpty),
                        NonNegative (NonNegative), Positive (Positive), chooseInt, elements,
                        functionMap, getNonEmpty, getNonNegative, getPositive, oneof, variant)
import Test.QuickCheck.Instances.Containers ()

deriving via Credential instance Arbitrary ColdCommitteeCredential

deriving via Credential instance CoArbitrary ColdCommitteeCredential

instance Function ColdCommitteeCredential where
  {-# INLINEABLE function #-}
  function = functionMap coerce ColdCommitteeCredential


deriving via Credential instance Arbitrary HotCommitteeCredential

deriving via Credential instance CoArbitrary HotCommitteeCredential

instance Function HotCommitteeCredential where
  {-# INLINEABLE function #-}
  function = functionMap coerce HotCommitteeCredential


deriving via Credential instance Arbitrary DRepCredential

deriving via Credential instance CoArbitrary DRepCredential

instance Function DRepCredential where
  {-# INLINEABLE function #-}
  function = functionMap coerce DRepCredential


{- | This instance has equal chance of generating always-abstain,
always-no-confidence and credential \'arms\'. Use this instance with this in
mind.
-}
instance Arbitrary DRep where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ DRep <$> arbitrary
      , pure DRepAlwaysAbstain
      , pure DRepAlwaysNoConfidence
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    DRep cred -> DRep <$> shrink cred
    _ -> []

instance CoArbitrary DRep where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    DRep cred -> variant (0 :: Int) . coarbitrary cred
    DRepAlwaysAbstain -> variant (1 :: Int)
    DRepAlwaysNoConfidence -> variant (2 :: Int)

instance Function DRep where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: DRep -> Maybe (Maybe DRepCredential)
      into = \case
        DRep cred -> Just (Just cred)
        DRepAlwaysAbstain -> Nothing
        DRepAlwaysNoConfidence -> Just Nothing

      outOf :: Maybe (Maybe DRepCredential) -> DRep
      outOf = \case
        Nothing -> DRepAlwaysAbstain
        Just Nothing -> DRepAlwaysNoConfidence
        Just (Just cred) -> DRep cred


instance Arbitrary Delegatee where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ DelegStake <$> arbitrary
      , DelegVote <$> arbitrary
      , DelegStakeVote <$> arbitrary <*> arbitrary
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    DelegStake pkh -> DelegStake <$> shrink pkh
    DelegVote drep -> DelegVote <$> shrink drep
    DelegStakeVote pkh drep ->
      [DelegStakeVote pkh' drep | pkh' <- shrink pkh] ++
      [DelegStakeVote pkh drep' | drep' <- shrink drep]

instance CoArbitrary Delegatee where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    DelegStake pkh -> variant (0 :: Int) . coarbitrary pkh
    DelegVote drep -> variant (1 :: Int) . coarbitrary drep
    DelegStakeVote pkh drep -> variant (2 :: Int) . coarbitrary pkh . coarbitrary drep

instance Function Delegatee where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        Delegatee ->
        Either PubKeyHash (Either DRep (PubKeyHash, DRep))
      into = \case
        DelegStake pkh -> Left pkh
        DelegVote drep -> Right (Left drep)
        DelegStakeVote pkh drep -> Right (Right (pkh, drep))

      outOf ::
        Either PubKeyHash (Either DRep (PubKeyHash, DRep)) ->
        Delegatee
      outOf = \case
        Left pkh -> DelegStake pkh
        Right (Left drep) -> DelegVote drep
        Right (Right (pkh, drep)) -> DelegStakeVote pkh drep


instance Arbitrary TxCert where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ TxCertRegStaking <$> arbitrary <*> arbitrary
      , TxCertUnRegStaking <$> arbitrary <*> arbitrary
      , TxCertDelegStaking <$> arbitrary <*> arbitrary
      , TxCertRegDeleg <$> arbitrary <*> arbitrary <*> arbitrary
      , TxCertRegDRep <$> arbitrary <*> arbitrary
      , TxCertUpdateDRep <$> arbitrary
      , TxCertUnRegDRep <$> arbitrary <*> arbitrary
      , TxCertPoolRegister <$> arbitrary <*> arbitrary
      , -- epoch must be positive for this to make any sense
        TxCertPoolRetire <$> arbitrary <*> (getPositive <$> arbitrary)
      , TxCertAuthHotCommittee <$> arbitrary <*> arbitrary
      , TxCertResignColdCommittee <$> arbitrary
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    TxCertRegStaking cred mLovelace ->
      [TxCertRegStaking cred' mLovelace | cred' <- shrink cred] ++
      [TxCertRegStaking cred mLovelace' | mLovelace' <- shrink mLovelace]
    TxCertUnRegStaking cred mLovelace ->
      [TxCertUnRegStaking cred' mLovelace | cred' <- shrink cred] ++
      [TxCertUnRegStaking cred mLovelace' | mLovelace' <- shrink mLovelace]
    TxCertDelegStaking cred deleg ->
      [TxCertDelegStaking cred' deleg | cred' <- shrink cred] ++
      [TxCertDelegStaking cred deleg' | deleg' <- shrink deleg]
    TxCertRegDeleg cred deleg lovelace ->
      [TxCertRegDeleg cred' deleg lovelace | cred' <- shrink cred] ++
      [TxCertRegDeleg cred deleg' lovelace | deleg' <- shrink deleg] ++
      [TxCertRegDeleg cred deleg lovelace' | lovelace' <- shrink lovelace]
    TxCertRegDRep drepCred lovelace ->
      [TxCertRegDRep drepCred' lovelace | drepCred' <- shrink drepCred] ++
      [TxCertRegDRep drepCred lovelace' | lovelace' <- shrink lovelace]
    TxCertUpdateDRep drepCred -> TxCertUpdateDRep <$> shrink drepCred
    TxCertUnRegDRep drepCred lovelace ->
      [TxCertUnRegDRep drepCred' lovelace | drepCred' <- shrink drepCred] ++
      [TxCertUnRegDRep drepCred lovelace' | lovelace' <- shrink lovelace]
    TxCertPoolRegister pkh vrf ->
      [TxCertPoolRegister pkh' vrf | pkh' <- shrink pkh] ++
      [TxCertPoolRegister pkh vrf' | vrf' <- shrink vrf]
    TxCertPoolRetire pkh epoch ->
      [TxCertPoolRetire pkh' epoch | pkh' <- shrink pkh] ++
      [TxCertPoolRetire pkh epoch' | epoch' <- shrink epoch]
    TxCertAuthHotCommittee cold hot ->
      [TxCertAuthHotCommittee cold' hot | cold' <- shrink cold] ++
      [TxCertAuthHotCommittee cold hot' | hot' <- shrink hot]
    TxCertResignColdCommittee cold -> TxCertResignColdCommittee <$> shrink cold

instance CoArbitrary TxCert where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    TxCertRegStaking cred mLovelace ->
      variant (0 :: Int) . coarbitrary cred . coarbitrary mLovelace
    TxCertUnRegStaking cred mLovelace ->
      variant (1 :: Int) . coarbitrary cred . coarbitrary mLovelace
    TxCertDelegStaking cred deleg ->
      variant (2 :: Int) . coarbitrary cred . coarbitrary deleg
    TxCertRegDeleg cred deleg lovelace ->
      variant (3 :: Int) . coarbitrary cred . coarbitrary deleg . coarbitrary lovelace
    TxCertRegDRep drepCred lovelace ->
      variant (4 :: Int) . coarbitrary drepCred . coarbitrary lovelace
    TxCertUpdateDRep drepCred ->
      variant (5 :: Int) . coarbitrary drepCred
    TxCertUnRegDRep drepCred lovelace ->
      variant (6 :: Int) . coarbitrary drepCred . coarbitrary lovelace
    TxCertPoolRegister pkh pkh' ->
      variant (7 :: Int) . coarbitrary pkh . coarbitrary pkh'
    TxCertPoolRetire pkh epoch ->
      variant (8 :: Int) . coarbitrary pkh . coarbitrary epoch
    TxCertAuthHotCommittee cold hot ->
      variant (9 :: Int) . coarbitrary cold . coarbitrary hot
    TxCertResignColdCommittee cold ->
      variant (10 :: Int) . coarbitrary cold

instance Function TxCert where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        TxCert ->
        Either
          (Credential, Maybe Lovelace)
          ( Either
              (Credential, Maybe Lovelace)
              ( Either
                  (Credential, Delegatee)
                  ( Either
                      (Credential, Delegatee, Lovelace)
                      ( Either
                          (DRepCredential, Lovelace)
                          ( Either
                              DRepCredential
                              ( Either
                                  (DRepCredential, Lovelace)
                                  ( Either
                                      (PubKeyHash, PubKeyHash)
                                      ( Either
                                          (PubKeyHash, Integer)
                                          ( Either (ColdCommitteeCredential, HotCommitteeCredential)
                                            ColdCommitteeCredential
                                          )
                                      )
                                  )
                              )
                          )
                      )
                  )
              )
          )
      into = \case
        TxCertRegStaking cred mLovelace ->
          Left (cred, mLovelace)
        TxCertUnRegStaking cred mLovelace ->
          Right (Left (cred, mLovelace))
        TxCertDelegStaking cred deleg ->
          Right (Right (Left (cred, deleg)))
        TxCertRegDeleg cred deleg lovelace ->
          Right (Right (Right (Left (cred, deleg, lovelace))))
        TxCertRegDRep drepCred lovelace ->
          Right (Right (Right (Right (Left (drepCred, lovelace)))))
        TxCertUpdateDRep drepCred ->
          Right (Right (Right (Right (Right (Left drepCred)))))
        TxCertUnRegDRep drepCred lovelace ->
          Right (Right (Right (Right (Right (Right (Left (drepCred, lovelace)))))))
        TxCertPoolRegister pkh pkh' ->
          Right (Right (Right (Right (Right (Right (Right (Left (pkh, pkh'))))))))
        TxCertPoolRetire pkh epoch ->
          Right (Right (Right (Right (Right (Right (Right (Right (Left (pkh, epoch)))))))))
        TxCertAuthHotCommittee hot cold ->
          Right (Right (Right (Right (Right (Right (Right (Right (Right (Left (hot, cold))))))))))
        TxCertResignColdCommittee cold ->
          Right (Right (Right (Right (Right (Right (Right (Right (Right (Right cold)))))))))

      outOf ::
        Either
          (Credential, Maybe Lovelace)
          ( Either
              (Credential, Maybe Lovelace)
              ( Either
                  (Credential, Delegatee)
                  ( Either
                      (Credential, Delegatee, Lovelace)
                      ( Either
                          (DRepCredential, Lovelace)
                          ( Either
                              DRepCredential
                              ( Either
                                  (DRepCredential, Lovelace)
                                  ( Either
                                      (PubKeyHash, PubKeyHash)
                                      ( Either
                                          (PubKeyHash, Integer)
                                          ( Either (ColdCommitteeCredential, HotCommitteeCredential)
                                            ColdCommitteeCredential
                                          )
                                      )
                                  )
                              )
                          )
                      )
                  )
              )
          ) ->
        TxCert
      outOf = \case
        Left (cred, mLovelace) ->
          TxCertRegStaking cred mLovelace
        Right (Left (cred, mLovelace)) ->
          TxCertUnRegStaking cred mLovelace
        Right (Right (Left (cred, deleg))) ->
          TxCertDelegStaking cred deleg
        Right (Right (Right (Left (cred, deleg, lovelace)))) ->
          TxCertRegDeleg cred deleg lovelace
        Right (Right (Right (Right (Left (drepCred, lovelace))))) ->
          TxCertRegDRep drepCred lovelace
        Right (Right (Right (Right (Right (Left drepCred))))) ->
          TxCertUpdateDRep drepCred
        Right (Right (Right (Right (Right (Right (Left (drepCred, lovelace))))))) ->
          TxCertUnRegDRep drepCred lovelace
        Right (Right (Right (Right (Right (Right (Right (Left (pkh, pkh')))))))) ->
          TxCertPoolRegister pkh pkh'
        Right (Right (Right (Right (Right (Right (Right (Right (Left (pkh, epoch))))))))) ->
          TxCertPoolRetire pkh epoch
        Right (Right (Right (Right (Right (Right (Right (Right (Right (Left (hot, cold)))))))))) ->
          TxCertAuthHotCommittee hot cold
        Right (Right (Right (Right (Right (Right (Right (Right (Right (Right cold))))))))) ->
          TxCertResignColdCommittee cold


instance Arbitrary Voter where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ CommitteeVoter <$> arbitrary
      , DRepVoter <$> arbitrary
      , StakePoolVoter <$> arbitrary
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    CommitteeVoter hcc -> CommitteeVoter <$> shrink hcc
    DRepVoter drepCred -> DRepVoter <$> shrink drepCred
    StakePoolVoter pkh -> StakePoolVoter <$> shrink pkh

instance CoArbitrary Voter where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    CommitteeVoter hcc -> variant (0 :: Int) . coarbitrary hcc
    DRepVoter drepCred -> variant (1 :: Int) . coarbitrary drepCred
    StakePoolVoter pkh -> variant (2 :: Int) . coarbitrary pkh

instance Function Voter where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        Voter ->
        Either HotCommitteeCredential (Either DRepCredential PubKeyHash)
      into = \case
        CommitteeVoter hcc -> Left hcc
        DRepVoter drepCred -> Right (Left drepCred)
        StakePoolVoter pkh -> Right (Right pkh)

      outOf ::
        Either HotCommitteeCredential (Either DRepCredential PubKeyHash) ->
        Voter
      outOf = \case
        Left hcc -> CommitteeVoter hcc
        Right (Left drepCred) -> DRepVoter drepCred
        Right (Right pkh) -> StakePoolVoter pkh


-- | Does not shrink (as there's not much point).
instance Arbitrary Vote where
  {-# INLINEABLE arbitrary #-}
  arbitrary = elements [VoteNo, VoteYes, Abstain]

instance CoArbitrary Vote where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    VoteNo -> variant (0 :: Int)
    VoteYes -> variant (1 :: Int)
    Abstain -> variant (2 :: Int)

instance Function Vote where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: Vote -> Int
      into = \case
        VoteNo -> 0
        VoteYes -> 1
        _ -> 2

      outOf :: Int -> Vote
      outOf = \case
        0 -> VoteNo
        1 -> VoteYes
        _ -> Abstain


deriving via Blake2b256Hash instance Arbitrary TxId

deriving via Blake2b256Hash instance CoArbitrary TxId

instance Function TxId where
  {-# INLINEABLE function #-}
  function = functionMap coerce TxId


instance Arbitrary GovernanceActionId where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    GovernanceActionId
      <$> arbitrary
      <*> (getNonNegative <$> arbitrary)

  {-# INLINEABLE shrink #-}
  shrink (GovernanceActionId tid ix) =
    [GovernanceActionId tid' ix | tid' <- shrink tid] ++
    [GovernanceActionId tid ix' | NonNegative ix' <- shrink (NonNegative ix)]

instance CoArbitrary GovernanceActionId where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (GovernanceActionId tid ix) =
    coarbitrary tid . coarbitrary ix

instance Function GovernanceActionId where
  {-# INLINEABLE function #-}
  function = functionMap (\(GovernanceActionId tid ix) -> (tid, ix)) (uncurry GovernanceActionId)


{- | Does not shrink the quorum, as this is surprisingly hard to do sensibly. We
assume the quorum is in the interval @(0, 1]@ (meaning anywhere from a single
voice to unanimity).
-}
instance Arbitrary Committee where
  {-# INLINEABLE arbitrary #-}
  arbitrary = do
    committee <- liftArbitrary (getPositive <$> arbitrary)
    -- We can't have a quorum of 0.0
    num <- chooseInt (1, 100)
    let quorum = Ratio.unsafeRatio (fromIntegral num) 100
    pure . Committee committee $ quorum

  {-# INLINEABLE shrink #-}
  shrink (Committee committee quorum) = do
    committee' <- liftShrink (fmap getPositive . shrink . Positive) committee
    guard (not . AssocMap.null $ committee')
    pure . Committee committee' $ quorum

instance CoArbitrary Committee where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (Committee committee quorum) =
    coarbitrary committee
      . coarbitrary (Ratio.numerator quorum)
      . coarbitrary (Ratio.denominator quorum)

instance Function Committee where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        Committee ->
        (Map ColdCommitteeCredential Integer, Integer, Integer)
      into (Committee committee quorum) =
        (committee, Ratio.numerator quorum, Ratio.denominator quorum)
      outOf ::
        (Map ColdCommitteeCredential Integer, Integer, Integer) ->
        Committee
      outOf (committee, num, den) =
        Committee committee . Ratio.unsafeRatio num $ den


deriving via (Maybe ScriptHash) instance Arbitrary Constitution

deriving via (Maybe ScriptHash) instance CoArbitrary Constitution

instance Function Constitution where
  {-# INLINEABLE function #-}
  function = functionMap coerce Constitution


instance Arbitrary ProtocolVersion where
  {-# INLINEABLE arbitrary #-}
  arbitrary = do
    NonNegative major <- arbitrary
    NonNegative minor <- arbitrary
    pure . ProtocolVersion major $ minor

  {-# INLINEABLE shrink #-}
  shrink (ProtocolVersion major minor) =
    [ProtocolVersion major' minor | NonNegative major' <- shrink (NonNegative major)] ++
    [ProtocolVersion major minor' | NonNegative minor' <- shrink (NonNegative minor)]

instance CoArbitrary ProtocolVersion where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (ProtocolVersion major minor) =
    coarbitrary major . coarbitrary minor

instance Function ProtocolVersion where
  {-# INLINEABLE function #-}
  function =
    functionMap
      (\(ProtocolVersion maj' min') -> (maj', min'))
      (uncurry ProtocolVersion)

{- | Currently only generates a map with integer keys in the range 0-33, with random values.
Does not shrink.
-}
instance Arbitrary ChangedParameters where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    ChangedParameters . Builtins.mkMap <$> do
      keyList <- liftArbitrary (chooseInt (0, 33))
      let keySet = Set.fromList keyList
      traverse (\k -> (Builtins.mkI . fromIntegral $ k,) <$> arbitrary) . Set.toList $ keySet

deriving via PlutusTx.BuiltinData instance CoArbitrary ChangedParameters

instance Function ChangedParameters where
  {-# INLINEABLE function #-}
  function = functionMap coerce ChangedParameters


-- TODO: Technically this can generate nonsensical instances (such as committee
-- members without keys), and we need to fix this.

instance Arbitrary GovernanceAction where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ ParameterChange <$> arbitrary <*> arbitrary <*> arbitrary
      , HardForkInitiation <$> arbitrary <*> arbitrary
      , TreasuryWithdrawals <$> arbitrary <*> arbitrary
      , NoConfidence <$> arbitrary
      , UpdateCommittee
          <$> arbitrary
          <*> arbitrary
          <*> arbitrary
          <*> (Ratio.unsafeRatio . fromIntegral <$> chooseInt (1, 100) <*> pure 100)
      , NewConstitution <$> arbitrary <*> arbitrary
      , pure InfoAction
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    ParameterChange mgid cp msh ->
      [ParameterChange mgid' cp msh | mgid' <- shrink mgid] ++
      [ParameterChange mgid cp' msh | cp' <- shrink cp] ++
      [ParameterChange mgid cp msh' | msh' <- shrink msh]
    HardForkInitiation mgid v ->
      [HardForkInitiation mgid' v | mgid' <- shrink mgid] ++
      [HardForkInitiation mgid v' | v' <- shrink v]
    TreasuryWithdrawals wdrls msh ->
      [TreasuryWithdrawals wdrls' msh | wdrls' <- shrink wdrls] ++
      [TreasuryWithdrawals wdrls msh' | msh' <- shrink msh]
    NoConfidence msh -> NoConfidence <$> shrink msh
    -- No quorum shrinking
    UpdateCommittee mgid creds mems quorum ->
      [UpdateCommittee mgid' creds mems quorum | mgid' <- shrink mgid] ++
      [UpdateCommittee mgid creds' mems quorum | creds' <- shrink creds] ++
      [UpdateCommittee mgid creds mems' quorum | mems' <- shrink mems]
    NewConstitution mgid c -> NewConstitution <$> shrink mgid <*> shrink c
    _ -> []

instance CoArbitrary GovernanceAction where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    ParameterChange mgid cp msh ->
      variant (0 :: Int) . coarbitrary mgid . coarbitrary cp . coarbitrary msh
    HardForkInitiation mgid v ->
      variant (1 :: Int) . coarbitrary mgid . coarbitrary v
    TreasuryWithdrawals wdrls msh ->
      variant (2 :: Int) . coarbitrary wdrls . coarbitrary msh
    NoConfidence msh ->
      variant (3 :: Int) . coarbitrary msh
    UpdateCommittee mgid creds mems quorum ->
      variant (4 :: Int)
        . coarbitrary mgid
        . coarbitrary creds
        . coarbitrary mems
        . coarbitrary (Ratio.numerator quorum)
        . coarbitrary (Ratio.denominator quorum)
    NewConstitution mgid c ->
      variant (5 :: Int) . coarbitrary mgid . coarbitrary c
    InfoAction -> variant (6 :: Int)

instance Function GovernanceAction where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        GovernanceAction ->
        Maybe
          ( Either
              (Maybe GovernanceActionId, ChangedParameters, Maybe ScriptHash)
              ( Either
                  (Maybe GovernanceActionId, ProtocolVersion)
                  ( Either
                      (Map Credential Lovelace, Maybe ScriptHash)
                      ( Either
                          (Maybe GovernanceActionId)
                          ( Either
                            (Maybe GovernanceActionId, [ColdCommitteeCredential]
                            , Map ColdCommitteeCredential Integer, Integer, Integer)
                            (Maybe GovernanceActionId, Constitution)
                          )
                      )
                  )
              )
          )
      into = \case
        InfoAction -> Nothing
        ParameterChange mgid cp msh -> Just (Left (mgid, cp, msh))
        HardForkInitiation mgid v -> Just (Right (Left (mgid, v)))
        TreasuryWithdrawals wdrls msh -> Just (Right (Right (Left (wdrls, msh))))
        NoConfidence msh -> Just (Right (Right (Right (Left msh))))
        UpdateCommittee mgid creds mems quorum ->
          Just (Right (Right (Right (Right (Left ( mgid
                                                 , creds
                                                 , mems
                                                 , Ratio.numerator quorum
                                                 , Ratio.denominator quorum))))))
        NewConstitution mgid c ->
          Just (Right (Right (Right (Right (Right (mgid, c))))))

      outOf ::
        Maybe
          ( Either
              (Maybe GovernanceActionId, ChangedParameters, Maybe ScriptHash)
              ( Either
                  (Maybe GovernanceActionId, ProtocolVersion)
                  ( Either
                      (Map Credential Lovelace, Maybe ScriptHash)
                      ( Either
                          (Maybe GovernanceActionId)
                          ( Either
                              ( Maybe GovernanceActionId
                              , [ColdCommitteeCredential]
                              , Map ColdCommitteeCredential Integer
                              , Integer
                              , Integer
                              )
                              (Maybe GovernanceActionId, Constitution)
                          )
                      )
                  )
              )
          ) ->
        GovernanceAction
      outOf = \case
        Nothing -> InfoAction
        Just (Left (mgid, cp, msh)) -> ParameterChange mgid cp msh
        Just (Right (Left (mgid, v))) -> HardForkInitiation mgid v
        Just (Right (Right (Left (wdrls, msh)))) -> TreasuryWithdrawals wdrls msh
        Just (Right (Right (Right (Left msh)))) -> NoConfidence msh
        Just (Right (Right (Right (Right (Left (mgid, creds, mems, n, d)))))) ->
          UpdateCommittee mgid creds mems (Ratio.unsafeRatio n d)
        Just (Right (Right (Right (Right (Right (mgid, c)))))) ->
          NewConstitution mgid c


instance Arbitrary ProposalProcedure where
  {-# INLINEABLE arbitrary #-}
  arbitrary = ProposalProcedure <$> arbitrary <*> arbitrary <*> arbitrary

  {-# INLINEABLE shrink #-}
  shrink (ProposalProcedure dep raddr ga) =
    [ProposalProcedure dep' raddr ga | dep' <- shrink dep] ++
    [ProposalProcedure dep raddr' ga | raddr' <- shrink raddr] ++
    [ProposalProcedure dep raddr ga' | ga' <- shrink ga]

instance CoArbitrary ProposalProcedure where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (ProposalProcedure dep raddr ga) =
    coarbitrary dep . coarbitrary raddr . coarbitrary ga

instance Function ProposalProcedure where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        ProposalProcedure ->
        (Lovelace, Credential, GovernanceAction)
      into (ProposalProcedure dep raddr ga) = (dep, raddr, ga)

      outOf ::
        (Lovelace, Credential, GovernanceAction) ->
        ProposalProcedure
      outOf (dep, raddr, ga) = ProposalProcedure dep raddr ga


instance Arbitrary TxOutRef where
  {-# INLINEABLE arbitrary #-}
  arbitrary = TxOutRef <$> arbitrary <*> (getNonNegative <$> arbitrary)

  {-# INLINEABLE shrink #-}
  shrink (TxOutRef tid ix) =
    [TxOutRef tid' ix | tid' <- shrink tid] ++
    [TxOutRef tid ix' | NonNegative ix' <- shrink (NonNegative ix)]

instance CoArbitrary TxOutRef where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxOutRef tid ix) =
    coarbitrary tid . coarbitrary ix

instance Function TxOutRef where
  {-# INLINEABLE function #-}
  function = functionMap (\(TxOutRef tid ix) -> (tid, ix)) (uncurry TxOutRef)


instance Arbitrary ScriptPurpose where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ Minting <$> arbitrary
      , Spending <$> arbitrary
      , Rewarding <$> arbitrary
      , Certifying . getNonNegative <$> arbitrary <*> arbitrary
      , Voting <$> arbitrary
      , Proposing . getNonNegative <$> arbitrary <*> arbitrary
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    Minting cs -> Minting <$> shrink cs
    Spending txo -> Spending <$> shrink txo
    Rewarding cred -> Rewarding <$> shrink cred
    Certifying ix cert ->
      [Certifying ix' cert | NonNegative ix' <- shrink (NonNegative ix)] ++
      [Certifying ix cert' | cert' <- shrink cert]
    Voting voter -> Voting <$> shrink voter
    Proposing ix pp ->
      [Proposing ix' pp | NonNegative ix' <- shrink (NonNegative ix)] ++
      [Proposing ix pp' | pp' <- shrink pp]

instance CoArbitrary ScriptPurpose where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    Minting cs -> variant (0 :: Int) . coarbitrary cs
    Spending txo -> variant (1 :: Int) . coarbitrary txo
    Rewarding cred -> variant (2 :: Int) . coarbitrary cred
    Certifying ix cert -> variant (3 :: Int) . coarbitrary ix . coarbitrary cert
    Voting voter -> variant (4 :: Int) . coarbitrary voter
    Proposing ix pp -> variant (5 :: Int) . coarbitrary ix . coarbitrary pp

instance Function ScriptPurpose where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        ScriptPurpose ->
        Either
          CurrencySymbol
          ( Either
              TxOutRef
              ( Either
                  Credential
                  ( Either
                      (Integer, TxCert)
                      ( Either Voter (Integer, ProposalProcedure)
                      )
                  )
              )
          )
      into = \case
        Minting cs -> Left cs
        Spending txo -> Right (Left txo)
        Rewarding cred -> Right (Right (Left cred))
        Certifying ix cert -> Right (Right (Right (Left (ix, cert))))
        Voting voter -> Right (Right (Right (Right (Left voter))))
        Proposing ix pp -> Right (Right (Right (Right (Right (ix, pp)))))

      outOf ::
        Either
          CurrencySymbol
          ( Either
              TxOutRef
              ( Either
                  Credential
                  ( Either
                      (Integer, TxCert)
                      ( Either Voter (Integer, ProposalProcedure)
                      )
                  )
              )
          ) ->
        ScriptPurpose
      outOf = \case
        Left cs -> Minting cs
        Right (Left txo) -> Spending txo
        Right (Right (Left cred)) -> Rewarding cred
        Right (Right (Right (Left (ix, cert)))) -> Certifying ix cert
        Right (Right (Right (Right (Left voter)))) -> Voting voter
        Right (Right (Right (Right (Right (ix, pp))))) -> Proposing ix pp

instance Arbitrary ScriptInfo where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ MintingScript <$> arbitrary
      , SpendingScript <$> arbitrary <*> arbitrary
      , RewardingScript <$> arbitrary
      , CertifyingScript . getNonNegative <$> arbitrary <*> arbitrary
      , VotingScript <$> arbitrary
      , ProposingScript . getNonNegative <$> arbitrary <*> arbitrary
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    MintingScript cs -> MintingScript <$> shrink cs
    SpendingScript outRef mdat ->
      [SpendingScript outRef' mdat | outRef' <- shrink outRef] ++
      [SpendingScript outRef mdat' | mdat' <- shrink mdat]
    RewardingScript cred -> RewardingScript <$> shrink cred
    CertifyingScript ix cert ->
      [CertifyingScript ix' cert | NonNegative ix' <- shrink (NonNegative ix)] ++
      [CertifyingScript ix cert' | cert' <- shrink cert]
    VotingScript voter -> VotingScript <$> shrink voter
    ProposingScript ix pp ->
      [ProposingScript ix' pp | NonNegative ix' <- shrink (NonNegative ix)] ++
      [ProposingScript ix pp' | pp' <- shrink pp]

instance CoArbitrary ScriptInfo where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    MintingScript cs -> variant (0 :: Int) . coarbitrary cs
    SpendingScript txo dat -> variant (1 :: Int) . coarbitrary txo . coarbitrary dat
    RewardingScript cred -> variant (2 :: Int) . coarbitrary cred
    CertifyingScript idx cert -> variant (3 :: Int) . coarbitrary idx . coarbitrary cert
    VotingScript voter -> variant (4 :: Int) . coarbitrary voter
    ProposingScript idx prc -> variant (5 :: Int) . coarbitrary idx . coarbitrary prc

instance Function ScriptInfo where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        ScriptInfo ->
        Either CurrencySymbol
          (Either (TxOutRef, Maybe Datum)
           (Either Credential
            (Either (Integer, TxCert)
              (Either Voter (Integer, ProposalProcedure)))))
      into = \case
        MintingScript cs -> Left cs
        SpendingScript txo dat -> Right (Left (txo, dat))
        RewardingScript cred -> Right (Right (Left cred))
        CertifyingScript idx cert -> Right (Right (Right (Left (idx, cert))))
        VotingScript voter -> Right (Right (Right (Right (Left voter))))
        ProposingScript idx prc -> Right (Right (Right (Right (Right (idx, prc)))))

      outOf ::
        Either CurrencySymbol
          (Either (TxOutRef, Maybe Datum)
           (Either Credential
            (Either (Integer, TxCert)
              (Either Voter (Integer, ProposalProcedure))))) ->
        ScriptInfo
      outOf = \case
        Left cs -> MintingScript cs
        Right (Left (txo, dat)) -> SpendingScript txo dat
        Right (Right (Left cred)) -> RewardingScript cred
        Right (Right (Right (Left (idx, cert)))) -> CertifyingScript idx cert
        Right (Right (Right (Right (Left voter)))) -> VotingScript voter
        Right (Right (Right (Right (Right (idx, prc))))) -> ProposingScript idx prc

instance Arbitrary TxInInfo where
  {-# INLINEABLE arbitrary #-}
  arbitrary = TxInInfo <$> arbitrary <*> arbitrary

  {-# INLINEABLE shrink #-}
  shrink (TxInInfo toutref tout) =
    [TxInInfo toutref' tout | toutref' <- shrink toutref] ++
    [TxInInfo toutref tout' | tout' <- shrink tout]

instance CoArbitrary TxInInfo where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxInInfo toutref tout) = coarbitrary toutref . coarbitrary tout

instance Function TxInInfo where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: TxInInfo -> (TxOutRef, TxOut)
      into (TxInInfo toutref tout) = (toutref, tout)

      outOf :: (TxOutRef, TxOut) -> TxInInfo
      outOf (toutref, tout) = TxInInfo toutref tout

-- TODO: invariants

instance Arbitrary TxInfo where
  {-# INLINEABLE arbitrary #-}
  arbitrary = do
    ins <- getNonEmpty <$> arbitrary
    routs <- arbitrary
    outs <- getNonEmpty <$> arbitrary
    fee <- arbitrary
    mint <- arbitrary
    cert <- arbitrary
    wdrl <- arbitrary
    valid <- arbitrary
    sigs <- Set.toList <$> arbitrary
    reds <- arbitrary
    dats <- arbitrary
    tid <- arbitrary
    votes <- arbitrary
    pps <- arbitrary
    currT <- arbitrary
    tDonation <- arbitrary
    pure
      . TxInfo ins routs outs fee mint cert wdrl valid sigs reds dats tid votes pps currT
      $ tDonation

  {-# INLINEABLE shrink #-}
  shrink (TxInfo ins routs outs fee mint cert wdrl val sigs rds dats tid votes pps cur don) =
    [TxInfo ins' routs outs fee mint cert wdrl val sigs rds dats tid votes pps cur don
    | NonEmpty ins' <- shrink (NonEmpty ins)] ++
    [TxInfo ins routs' outs fee mint cert wdrl val sigs rds dats tid votes pps cur don
    | routs' <- shrink routs] ++
    [TxInfo ins routs outs' fee mint cert wdrl val sigs rds dats tid votes pps cur don
    | NonEmpty outs' <- shrink (NonEmpty outs)] ++
    [TxInfo ins routs outs fee' mint cert wdrl val sigs rds dats tid votes pps cur don
    | fee' <- shrink fee] ++
    [TxInfo ins routs outs fee mint' cert wdrl val sigs rds dats tid votes pps cur don
    | mint' <- shrink mint] ++
    [TxInfo ins routs outs fee mint cert' wdrl val sigs rds dats tid votes pps cur don
    | cert' <- shrink cert] ++
    [TxInfo ins routs outs fee mint cert wdrl' val sigs rds dats tid votes pps cur don
    | wdrl' <- shrink wdrl] ++
    [TxInfo ins routs outs fee mint cert wdrl val' sigs rds dats tid votes pps cur don
    | val' <- shrink val] ++
    [TxInfo ins routs outs fee mint cert wdrl val sigs' rds dats tid votes pps cur don
    | sigs' <- shrink sigs] ++
    [TxInfo ins routs outs fee mint cert wdrl val sigs rds' dats tid votes pps cur don
    | rds' <- shrink rds] ++
    [TxInfo ins routs outs fee mint cert wdrl val sigs rds dats' tid votes pps cur don
    | dats' <- shrink dats] ++
    [TxInfo ins routs outs fee mint cert wdrl val sigs rds dats tid' votes pps cur don
    | tid' <- shrink tid] ++
    [TxInfo ins routs outs fee mint cert wdrl val sigs rds dats tid votes' pps cur don
    | votes' <- shrink votes] ++
    [TxInfo ins routs outs fee mint cert wdrl val sigs rds dats tid votes pps' cur don
    | pps' <- shrink pps] ++
    [TxInfo ins routs outs fee mint cert wdrl val sigs rds dats tid votes pps cur' don
    | cur' <- shrink cur] ++
    [TxInfo ins routs outs fee mint cert wdrl val sigs rds dats tid votes pps cur don'
    | don' <- shrink don]

instance CoArbitrary TxInfo where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (TxInfo ins routs outs fee mint cert wdrl val sigs rds dats tid votes pps cur don) =
    coarbitrary ins
    . coarbitrary routs
    . coarbitrary outs
    . coarbitrary fee
    . coarbitrary mint
    . coarbitrary cert
    . coarbitrary wdrl
    . coarbitrary val
    . coarbitrary sigs
    . coarbitrary rds
    . coarbitrary dats
    . coarbitrary tid
    . coarbitrary votes
    . coarbitrary pps
    . coarbitrary cur
    . coarbitrary don

instance Function TxInfo where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        TxInfo ->
        ( [TxInInfo]
        , [TxInInfo]
        , [TxOut]
        , Lovelace
        , MintValue
        , [TxCert]
        , ( Map Credential Lovelace
          , POSIXTimeRange
          , [PubKeyHash]
          , Map ScriptPurpose Redeemer
          , Map DatumHash Datum
          , TxId
          , ( Map Voter (Map GovernanceActionId Vote)
            , [ProposalProcedure]
            , Maybe Lovelace
            , Maybe Lovelace
            )
          )
        )
      into (TxInfo ins routs outs fee mint cert wdrl val sigs rds dats tid votes pps cur don) =
        (ins, routs, outs, fee, mint, cert,
          (wdrl, val, sigs, rds, dats, tid, (votes, pps, cur, don)))

      outOf ::
        ( [TxInInfo]
        , [TxInInfo]
        , [TxOut]
        , Lovelace
        , MintValue
        , [TxCert]
        , ( Map Credential Lovelace
          , POSIXTimeRange
          , [PubKeyHash]
          , Map ScriptPurpose Redeemer
          , Map DatumHash Datum
          , TxId
          , ( Map Voter (Map GovernanceActionId Vote)
            , [ProposalProcedure]
            , Maybe Lovelace
            , Maybe Lovelace
            )
          )
        ) ->
        TxInfo
      outOf
        (ins, routs, outs, fee, mint, cert,
          (wdrl, val, sigs, rds, dats, tid, (votes, pps, cur, don))) =
        TxInfo ins routs outs fee mint cert wdrl val sigs rds dats tid votes pps cur don


instance Arbitrary ScriptContext where
  {-# INLINEABLE arbitrary #-}
  arbitrary = ScriptContext <$> arbitrary <*> arbitrary <*> arbitrary

  {-# INLINEABLE shrink #-}
  shrink (ScriptContext tinfo red sinfo) =
    [ScriptContext tinfo' red sinfo | tinfo' <- shrink tinfo] ++
    [ScriptContext tinfo red' sinfo | red' <- shrink red] ++
    [ScriptContext tinfo red sinfo' | sinfo' <- shrink sinfo]

instance CoArbitrary ScriptContext where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary (ScriptContext tinfo red sinfo) =
    coarbitrary tinfo . coarbitrary red . coarbitrary sinfo

instance Function ScriptContext where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: ScriptContext -> (TxInfo, Redeemer, ScriptInfo)
      into (ScriptContext tinfo red sinfo) = (tinfo, red, sinfo)

      outOf :: (TxInfo, Redeemer, ScriptInfo) -> ScriptContext
      outOf (tinfo, red, sinfo) = ScriptContext tinfo red sinfo

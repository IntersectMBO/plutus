-- | Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction. This is, of course, limited by the maximum
-- number of inputs a transaction can have.
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
module Language.PlutusTx.Coordination.Contracts.CrowdFunding (
    -- * Campaign parameters
    Campaign(..)
    , CampaignActor
    -- * Functionality for campaign contributors
    , contribute
    -- * Functionality for campaign owners
    , collect
    , campaignAddress
    -- * Validator script
    , contributionScript
    ) where

import           Control.Applicative          (Applicative (..))
import           Control.Lens
import           Control.Monad                (void)
import           Data.Foldable                (foldl')
import qualified Data.Map                     as Map
import           Data.Maybe                   (fromMaybe)
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)

import qualified Language.PlutusTx            as PlutusTx
import qualified Ledger.Interval              as Interval
import           Ledger.Slot                  (SlotRange)
import qualified Ledger.Slot                  as Slot
import           Ledger                       (DataScript (..), Signature(..), PubKey (..),
                                               TxId, ValidatorScript (..), scriptTxIn, Slot(..))
import qualified Ledger                       as Ledger
import           Ledger.Validation            (PendingTx (..), PendingTxIn (..), PendingTxOut)
import qualified Ledger.Validation            as Validation
import qualified Ledger.Value.TH              as V
import qualified Ledger.Ada.TH                as Ada
import           Ledger.Ada                   (Ada)
import qualified Wallet.API                   as W
import           Wallet                       (EventHandler (..), EventTrigger, WalletAPI (..),
                                               WalletDiagnostics (..), andT, slotRangeT, createTxAndSubmit, fundsAtAddressT, throwOtherError,
                                               ownPubKeyTxOut, payToScript)

import           Prelude                    (Bool (..), fst, snd, ($), (.),
                                             (<$>), (==))

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Slot
    , campaignTarget             :: Ada
    , campaignCollectionDeadline :: Slot
    , campaignOwner              :: CampaignActor
    } deriving Generic

type CampaignActor = PubKey

PlutusTx.makeLift ''Campaign

collectionRange :: Campaign -> SlotRange
collectionRange cmp =
    W.interval (campaignDeadline cmp) (campaignCollectionDeadline cmp)

refundRange :: Campaign -> SlotRange
refundRange cmp =
    W.intervalFrom (campaignCollectionDeadline cmp)

data Redeemer = Collect | Refund
    deriving Generic

PlutusTx.makeLift ''Redeemer

-- | Contribute funds to the campaign (contributor)
--
contribute :: (WalletAPI m, WalletDiagnostics m)
    => Campaign
    -> Ada
    -> m ()
contribute cmp adaAmount = do
    let value = $$(Ada.toValue) adaAmount
    _ <- if $$(V.leq) value $$(V.zero) then throwOtherError "Must contribute a positive value" else pure ()
    ds <- DataScript . Ledger.lifted . W.pubKey <$> myKeyPair

    let range = W.interval 1 (campaignDeadline cmp)

    tx <- payToScript range (campaignAddress cmp) value ds
    logMsg "Submitted contribution"

    register (refundTrigger cmp) (refund (Ledger.hashTx tx) cmp)
    logMsg "Registered refund trigger"

-- | Register a [[EventHandler]] to collect all the funds of a campaign
--
collect :: (WalletAPI m, WalletDiagnostics m) => Campaign -> m ()
collect cmp = register (collectFundsTrigger cmp) $ EventHandler $ \_ -> do
        logMsg "Collecting funds"
        am <- watchedAddresses
        let scr        = contributionScript cmp
            contributions = am ^. at (campaignAddress cmp) . to (Map.toList . fromMaybe Map.empty)
            red        = Ledger.RedeemerScript $ Ledger.lifted $ Collect
            con (r, _) = scriptTxIn r scr red
            ins        = con <$> contributions
            value = foldl' $$(V.plus) $$(V.zero) $ Ledger.txOutValue . snd <$> contributions
            range = collectionRange cmp

        oo <- ownPubKeyTxOut value
        void $ createTxAndSubmit range (Set.fromList ins) [oo]

-- | The address of a [[Campaign]]
campaignAddress :: Campaign -> Ledger.Address
campaignAddress = Ledger.scriptAddress . contributionScript

-- | The validator script that determines whether the campaign owner can
--   retrieve the funds or the contributors can claim a refund.
--
--   Assume there is a campaign `c :: Campaign` with two contributors
--   (identified by public key pc_1 and pc_2) and one campaign owner (pco).
--   Each contributor creates a transaction, t_1 and t_2, whose outputs are
--   locked by the scripts `contributionScript c pc_1` and `contributionScript
--   c pc_1` respectively.
--   There are two outcomes for the campaign.
--   1. Campaign owner collects the funds from both contributors. In this case
--      the owner creates a single transaction with two inputs, referring to
--      t_1 and t_2. Each input contains the script `contributionScript c`
--      specialised to a contributor. This case is covered by the
--      definition for `payToOwner` below.
--   2. Refund. In this case each contributor creates a transaction with a
--      single input claiming back their part of the funds. This case is
--      covered by the `refundable` branch.
contributionScript :: Campaign -> ValidatorScript
contributionScript cmp  = ValidatorScript val where
    val = Ledger.applyScript inner (Ledger.lifted cmp)

    --   See note [Contracts and Validator Scripts] in
    --       Language.Plutus.Coordination.Contracts
    inner = $$(Ledger.compileScript [|| (\Campaign{..} (a :: CampaignActor) (act :: CampaignAction) (p :: PendingTx) ->
        let

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $$(PlutusTx.and)

            -- | Check that a pending transaction is signed by the private key
            --   of the given public key.
            signedBy :: PendingTx -> PubKey -> Bool
            signedBy = $$(Validation.txSignedBy)

            PendingTx ps outs _ _ _ range _ _ = p

            collRange :: SlotRange
            collRange = $$(Interval.interval) campaignDeadline campaignCollectionDeadline

            refndRange :: SlotRange
            refndRange = $$(Interval.from) campaignCollectionDeadline

            -- | The total ada value of all contributions
            totalInputs :: Ada
            totalInputs =
                let addToTotal (PendingTxIn _ _ vl) total = let adaVl = $$(Ada.fromValue) vl in $$(Ada.plus) total adaVl
                in $$(PlutusTx.foldr) addToTotal $$(Ada.zero) ps

            isValid = case act of
                Refund -> -- the "refund" branch
                    let
                        -- Check that all outputs are paid to the public key
                        -- of the contributor (that is, to the `a` argument of the data script)

                        contributorTxOut :: PendingTxOut -> Bool
                        contributorTxOut o = $$(PlutusTx.maybe) False (\pk -> $$(Validation.eqPubKey) pk a) ($$(Validation.pubKeyOutput) o)

                        contributorOnly = $$(PlutusTx.all) contributorTxOut outs

                        refundable   = $$(Slot.contains) refndRange range &&
                                        contributorOnly &&
                                        p `signedBy` a

                    in refundable
                Collect -> -- the "successful campaign" branch
                    let
                        payToOwner = $$(Slot.contains) collRange range &&
                                    $$(Ada.geq) totalInputs campaignTarget &&
                                    p `signedBy` campaignOwner
                    in payToOwner
        in
        if isValid then () else $$(PlutusTx.error) ()) ||])

-- | An event trigger that fires when a refund of campaign contributions can be claimed
refundTrigger :: Campaign -> EventTrigger
refundTrigger c = andT
    (fundsAtAddressT (campaignAddress c) $ W.intervalFrom ($$(Ada.adaValueOf) 1))
    (slotRangeT (refundRange c))

-- | An event trigger that fires when the funds for a campaign can be collected
collectFundsTrigger :: Campaign -> EventTrigger
collectFundsTrigger c = andT
    (fundsAtAddressT (campaignAddress c) $ W.intervalFrom $ ($$(Ada.toValue) (campaignTarget c)))
    (slotRangeT (collectionRange c))

-- | Claim a refund of our campaign contribution
refund :: (WalletAPI m, WalletDiagnostics m) => TxId -> Campaign -> EventHandler m
refund txid cmp = EventHandler $ \_ -> do
    logMsg "Claiming refund"
    am <- watchedAddresses
    let adr     = campaignAddress cmp
        utxo    = fromMaybe Map.empty $ am ^. at adr
        ourUtxo = Map.toList $ Map.filterWithKey (\k _ -> txid == Ledger.txOutRefId k) utxo
        scr   = contributionScript cmp
        red   = Ledger.RedeemerScript $ Ledger.lifted Refund
        i ref = scriptTxIn ref scr red
        inputs = Set.fromList $ i . fst <$> ourUtxo
        value  = foldl' $$(V.plus) $$(V.zero) $ Ledger.txOutValue . snd <$> ourUtxo

    out <- ownPubKeyTxOut value
    void $ createTxAndSubmit (refundRange cmp) inputs [out]

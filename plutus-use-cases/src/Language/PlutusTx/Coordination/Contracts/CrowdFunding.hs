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
    ) where

import           Control.Applicative          (Applicative (..))
import           Control.Lens
import           Control.Monad                (void)
import           Data.Foldable                (foldMap)
import qualified Data.Map                     as Map
import           Data.Maybe                   (fromMaybe)
import           Data.Monoid                  (Sum (..))
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)

import qualified Language.PlutusTx            as PlutusTx
import qualified Ledger.Interval              as Interval
import           Ledger.Interval              (SlotRange)
import           Ledger                       (DataScript (..), Signature(..), PubKey (..),
                                               TxId, ValidatorScript (..), Value (..), scriptTxIn, Slot(..))
import qualified Ledger                       as Ledger
import           Ledger.Validation            (PendingTx (..), PendingTxIn (..), PendingTxOut)
import qualified Ledger.Validation            as Validation
import qualified Wallet.API                   as W
import           Wallet                       (EventHandler (..), EventTrigger, WalletAPI (..),
                                               WalletDiagnostics (..), andT, slotRangeT, fundsAtAddressT, throwOtherError,
                                               ownPubKeyTxOut, payToScript, pubKey, createTxAndSubmit, signature)

import           Prelude                    (Bool (..), Int, Ord (..), fst, snd, ($), (.),
                                             (<$>), (==))

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Slot
    , campaignTarget             :: Value
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

data CampaignAction = Collect Signature | Refund Signature
    deriving Generic

PlutusTx.makeLift ''CampaignAction

-- | Contribute funds to the campaign (contributor)
--
contribute :: (WalletAPI m, WalletDiagnostics m)
    => Campaign
    -> Value
    -> m ()
contribute cmp value = do
    _ <- if value <= 0 then throwOtherError "Must contribute a positive value" else pure ()
    ds <- DataScript . Ledger.lifted . pubKey <$> myKeyPair

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
        keyPair <- myKeyPair
        let sig = signature keyPair
        let scr        = contributionScript cmp
            contributions = am ^. at (campaignAddress cmp) . to (Map.toList . fromMaybe Map.empty)
            red        = Ledger.RedeemerScript $ Ledger.lifted $ Collect sig
            con (r, _) = scriptTxIn r scr red
            ins        = con <$> contributions
            value = getSum $ foldMap (Sum . Ledger.txOutValue . snd) contributions
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
    inner = $$(Ledger.compileScript [|| (\Campaign{..} (act :: CampaignAction) (a :: CampaignActor) (p :: PendingTx) ->
        let

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $$(PlutusTx.and)
            
            infixl 6 +
            (+) :: Int -> Int -> Int
            (+) = $$(PlutusTx.plus)

            -- | Check that a pending transaction is signed by the private key
            --   of the given public key.
            signedBy :: PubKey -> Signature -> Bool
            signedBy (PubKey pk) (Signature s) = $$(PlutusTx.eq) pk s

            PendingTx ps outs _ _ _ range = p

            collRange :: SlotRange
            collRange = $$(Interval.interval) campaignDeadline campaignCollectionDeadline

            refndRange :: SlotRange
            refndRange = $$(Interval.from) campaignCollectionDeadline

            target :: Int
            target = let Value v = campaignTarget in v

            -- | The total value of all contributions
            totalInputs :: Int
            totalInputs =
                let v (PendingTxIn _ _ (Value vl)) = vl in
                $$(PlutusTx.foldr) (\i total -> total + v i) 0 ps

            isValid = case act of
                Refund sig -> -- the "refund" branch
                    let
                        -- Check that all outputs are paid to the public key
                        -- of the contributor (that is, to the `a` argument of the data script)

                        contributorTxOut :: PendingTxOut -> Bool
                        contributorTxOut o = $$(PlutusTx.maybe) False (\pk -> $$(Validation.eqPubKey) pk a) ($$(Validation.pubKeyOutput) o)

                        contributorOnly = $$(PlutusTx.all) contributorTxOut outs

                        refundable   = $$(Interval.contains) refndRange range &&
                                        contributorOnly &&
                                        a `signedBy` sig

                    in refundable
                Collect sig -> -- the "successful campaign" branch
                    let
                        payToOwner = $$(Interval.contains) collRange range &&
                                    $$(PlutusTx.geq) totalInputs target &&
                                    campaignOwner `signedBy` sig
                    in payToOwner
        in
        if isValid then () else $$(PlutusTx.error) ()) ||])

-- | An event trigger that fires when a refund of campaign contributions can be claimed
refundTrigger :: Campaign -> EventTrigger
refundTrigger c = andT
    (fundsAtAddressT (campaignAddress c) $ W.intervalFrom 1)
    (slotRangeT (refundRange c))

-- | An event trigger that fires when the funds for a campaign can be collected
collectFundsTrigger :: Campaign -> EventTrigger
collectFundsTrigger c = andT
    (fundsAtAddressT (campaignAddress c) $ W.intervalFrom $ campaignTarget c)
    (slotRangeT (collectionRange c))

-- | Claim a refund of our campaign contribution
refund :: (WalletAPI m, WalletDiagnostics m) => TxId -> Campaign -> EventHandler m
refund txid cmp = EventHandler $ \_ -> do
    logMsg "Claiming refund"
    am <- watchedAddresses
    keyPair <- myKeyPair
    let sig = signature keyPair
    let adr     = campaignAddress cmp
        utxo    = fromMaybe Map.empty $ am ^. at adr
        ourUtxo = Map.toList $ Map.filterWithKey (\k _ -> txid == Ledger.txOutRefId k) utxo
        scr   = contributionScript cmp
        red   = Ledger.RedeemerScript $ Ledger.lifted $ Refund sig
        i ref = scriptTxIn ref scr red
        inputs = Set.fromList $ i . fst <$> ourUtxo
        value  = getSum $ foldMap (Sum . Ledger.txOutValue . snd) ourUtxo

    out <- ownPubKeyTxOut value
    void $ createTxAndSubmit (refundRange cmp) inputs [out]

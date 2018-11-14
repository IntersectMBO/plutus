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
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Language.Plutus.Coordination.Contracts.CrowdFunding (
    -- * Campaign parameters
    Campaign(..)
    , CampaignActor
    -- * Functionality for campaign contributors
    , contribute
    -- * Functionality for campaign owners
    , collect
    , campaignAddress
    ) where

import           Control.Applicative        (Applicative (..))
import           Control.Lens
import           Control.Monad              (Monad (..), void)
import           Control.Monad.Error.Class  (MonadError (..))
import           Data.Foldable              (foldMap)
import qualified Data.Map                   as Map
import           Data.Maybe                 (fromMaybe)
import           Data.Monoid                (Sum (..))
import qualified Data.Set                   as Set
import           GHC.Generics               (Generic)

import           Language.Plutus.Lift       (LiftPlc (..), TypeablePlc (..))
import           Language.Plutus.Runtime    (Height (..), PendingTx (..), PendingTxIn (..), PendingTxOut, PubKey (..),
                                             ValidatorHash, Value (..))
import           Language.Plutus.TH         (plutus)
import qualified Language.Plutus.TH         as Builtins
import           Wallet.API                 (BlockchainAction (..), EventTrigger (..), Range (..), WalletAPI (..),
                                             WalletAPIError, andT, blockHeightT, fundsAtAddressT, otherError,
                                             ownPubKeyTxOut, payToScript, pubKey, signAndSubmit)
import           Wallet.UTXO                (DataScript (..), TxId', Validator (..), scriptTxIn)
import qualified Wallet.UTXO                as UTXO

import qualified Language.Plutus.Runtime.TH as TH
import           Prelude                    (Bool (..), Int, Num (..), Ord (..), fromIntegral, fst, snd, succ, ($), (.),
                                             (<$>), (==))

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Height
    , campaignTarget             :: Value
    , campaignCollectionDeadline :: Height
    , campaignOwner              :: CampaignActor
    } deriving Generic

type CampaignActor = PubKey

instance LiftPlc Campaign
instance TypeablePlc Campaign

data CampaignAction = Collect | Refund
    deriving Generic

instance LiftPlc CampaignAction
instance TypeablePlc CampaignAction

-- | Contribute funds to the campaign (contributor)
--
contribute :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Campaign
    -> Value
    -> m ()
contribute cmp value = do
    _ <- if value <= 0 then otherError "Must contribute a positive value" else pure ()
    ds <- DataScript . UTXO.lifted . pubKey <$> myKeyPair

    -- TODO: Remove duplicate definition of Value
    --       (Value = Integer in Haskell land but Value = Int in PLC land)
    let v' = UTXO.Value $ fromIntegral value
    tx <- payToScript (campaignAddress cmp) v' ds

    register (refundTrigger cmp) (refund (UTXO.hashTx tx) cmp)

-- | Register a [[BlockchainAction]] to collect all the funds of a campaign
--
collect :: (Monad m, WalletAPI m) => Campaign -> m ()
collect cmp = register (collectFundsTrigger cmp) $ BlockchainAction $ \_ am -> do
        let scr        = contributionScript cmp
            contributions = am ^. at (campaignAddress cmp) . to (Map.toList . fromMaybe Map.empty)
            red        = UTXO.Redeemer $ UTXO.lifted Collect
            con (r, _) = scriptTxIn r scr red
            ins        = con <$> contributions
            value = getSum $ foldMap (Sum . snd) contributions

        oo <- ownPubKeyTxOut value
        void $ signAndSubmit (Set.fromList ins) [oo]


-- | The address of a [[Campaign]]
campaignAddress :: Campaign -> UTXO.Address'
campaignAddress = UTXO.scriptAddress . contributionScript

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
contributionScript :: Campaign -> Validator
contributionScript cmp  = Validator val where
    val = UTXO.applyScript inner (UTXO.lifted cmp)

    --   See note [Contracts and Validator Scripts] in
    --       Language.Plutus.Coordination.Contracts
    inner = UTXO.fromPlcCode $(plutus [| (\Campaign{..} (act :: CampaignAction) (a :: CampaignActor) (p :: PendingTx ValidatorHash) ->
        let

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $(TH.and)

            -- | Check that a pending transaction is signed by the private key
            --   of the given public key.
            signedByT :: PendingTx ValidatorHash -> CampaignActor -> Bool
            signedByT = $(TH.txSignedBy)

            PendingTx ps outs _ _ (Height h) _ _ = p

            deadline :: Int
            deadline = let Height h' = campaignDeadline in h'

            collectionDeadline :: Int
            collectionDeadline = let Height h' = campaignCollectionDeadline in h'

            target :: Int
            target = let Value v = campaignTarget in v

            -- | The total value of all contributions
            totalInputs :: Int
            totalInputs =
                let v (PendingTxIn _ _ (Value vl)) = vl in
                $(TH.foldr) (\i total -> total + v i) 0 ps

            isValid = case act of
                Refund -> -- the "refund" branch
                    let
                        -- Check that all outputs are paid to the public key
                        -- of the contributor (that is, to the `a` argument of the data script)

                        contributorTxOut :: PendingTxOut -> Bool
                        contributorTxOut o = $(TH.maybe) False (\pk -> $(TH.eqPubKey) pk a) ($(TH.pubKeyOutput) o)

                        contributorOnly = $(TH.all) contributorTxOut outs

                        refundable   = h > collectionDeadline &&
                                                    contributorOnly &&
                                                    signedByT p a

                    in refundable
                Collect -> -- the "successful campaign" branch
                    let
                        payToOwner = h > deadline &&
                                    h <= collectionDeadline &&
                                    totalInputs >= target &&
                                    signedByT p campaignOwner
                    in payToOwner
        in
        if isValid then () else Builtins.error ()) |])

-- | An event trigger that fires when a refund of campaign contributions can be claimed
refundTrigger :: Campaign -> EventTrigger
refundTrigger c = andT
    (fundsAtAddressT (campaignAddress c) $ GEQ 1)
    (blockHeightT (GEQ $ fromIntegral $ succ $ getHeight $ campaignCollectionDeadline c))

-- | An event trigger that fires when the funds for a campaign can be collected
collectFundsTrigger :: Campaign -> EventTrigger
collectFundsTrigger c = andT
    (fundsAtAddressT (campaignAddress c) $ GEQ $ UTXO.Value $ fromIntegral $ campaignTarget c)
    (blockHeightT $ fromIntegral . getHeight <$> Interval (campaignDeadline c) (campaignCollectionDeadline c))

-- | Claim a refund of our campaign contribution
refund :: (Monad m, WalletAPI m) => TxId' -> Campaign -> BlockchainAction m
refund txid cmp = BlockchainAction $ \_ am -> do
    let adr     = campaignAddress cmp
        utxo    = fromMaybe Map.empty $ am ^. at adr
        ourUtxo = Map.toList $ Map.filterWithKey (\k _ -> txid == UTXO.txOutRefId k) utxo
        scr   = contributionScript cmp
        red   = UTXO.Redeemer $ UTXO.lifted Refund
        i ref = scriptTxIn ref scr red
        inputs = Set.fromList $ i . fst <$> ourUtxo
        value  = getSum $ foldMap (Sum . snd) ourUtxo

    out <- ownPubKeyTxOut value
    void $ signAndSubmit inputs [out]

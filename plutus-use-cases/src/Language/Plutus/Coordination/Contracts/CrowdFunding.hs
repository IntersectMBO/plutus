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
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Language.Plutus.Coordination.Contracts.CrowdFunding (
    -- * Campaign parameters
    Campaign(..)
    , CampaignActor
    -- * Functionality for campaign contributors
    , contribute
    , contributionScript
    , refund
    , refundTrigger
    -- * Functionality for campaign owners
    , collect
    , collectFundsTrigger
    ) where

import           Control.Applicative        (Applicative (..))
import           Control.Monad              (Monad (..))
import           Control.Monad.Error.Class  (MonadError (..))
import           Data.Foldable              (foldMap)
import           Data.Monoid                (Sum (..))
import qualified Data.Set                   as Set
import           GHC.Generics               (Generic)

import           Language.Plutus.Lift       (LiftPlc (..), TypeablePlc (..))
import           Language.Plutus.Runtime    (Height, PendingTx (..), PendingTxIn (..), PubKey (..), ValidatorHash,
                                             Value)
import           Language.Plutus.TH         (plutus)
import qualified Language.Plutus.TH         as Builtins
import           Wallet.API                 (EventTrigger (..), Range (..), WalletAPI (..), WalletAPIError, andT,
                                             blockHeightT, fundsAtAddressT, otherError, ownPubKeyTxOut, pubKey,
                                             signAndSubmit)
import           Wallet.UTXO                (Address', DataScript (..), TxOutRef', Validator (..), scriptTxIn,
                                             scriptTxOut)
import qualified Wallet.UTXO                as UTXO

import qualified Language.Plutus.Runtime.TH as TH
import           Prelude                    (Bool (..), Num (..), Ord (..), fromIntegral, snd, succ, ($), (.), (<$>))

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
    (payment, change) <- createPaymentWithChange v'
    let o = scriptTxOut v' (contributionScript cmp) ds

    signAndSubmit payment [o, change]

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
    inner = UTXO.fromPlcCode $(plutus [| (\Campaign{..} () (a :: CampaignActor) (p :: PendingTx ValidatorHash) ->
        let
            -- | Check that a transaction input is signed by the private key of the given
            --   public key.
            signedBy :: PendingTxIn -> CampaignActor -> Bool
            signedBy = $(TH.txInSignedBy)

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $(TH.and)

            -- | Check that a pending transaction is signed by the private key
            --   of the given public key.
            signedByT :: PendingTx ValidatorHash -> CampaignActor -> Bool
            signedByT = $(TH.txSignedBy)

            PendingTx _ _ _ _ h _ _ = p

            isValid = case p of
                PendingTx (ps::[PendingTxIn]) _ _ _ _ _ _ ->
                    case ps of
                        (pt1::PendingTxIn):(ps'::[PendingTxIn]) ->
                            case ps' of
                                (pt2::PendingTxIn):(_::[PendingTxIn]) ->
                                    -- the "successful campaign" branch
                                    let
                                        PendingTxIn _ _ v1 = pt1
                                        PendingTxIn _ _ v2 = pt2
                                        pledgedFunds = v1 + v2

                                        payToOwner = h > campaignDeadline &&
                                                    h <= campaignCollectionDeadline &&
                                                    pledgedFunds >= campaignTarget &&
                                                    signedByT p campaignOwner
                                    in payToOwner
                                (_::[PendingTxIn]) -> -- the "refund" branch
                                    let
                                        -- Check that a refund transaction only spends the
                                        -- amount that was pledged by the contributor
                                        -- identified by `a :: CampaignActor`
                                        contributorOnly = signedBy pt1 a
                                        refundable   = h > campaignCollectionDeadline &&
                                                                    contributorOnly &&
                                                                    signedByT p a
                                        -- In case of a refund, we can only collect the funds that
                                        -- were committed by this contributor
                                    in refundable
                        (_::[PendingTxIn]) -> False
        in
        if isValid then () else Builtins.error ()) |])

-- | Given the campaign data and the output from the contributing transaction,
--   make a trigger that fires when the transaction can be refunded.
refundTrigger :: Campaign -> Address' -> EventTrigger
refundTrigger Campaign{..} t = andT
    (fundsAtAddressT t  (GEQ 1))
    (blockHeightT (GEQ $ fromIntegral $ succ campaignCollectionDeadline))

-- | Given the public key of the campaign owner, generate an event trigger that
-- fires when the funds can be collected.
collectFundsTrigger :: Campaign -> Address' -> EventTrigger
collectFundsTrigger Campaign{..} ts = andT
    (fundsAtAddressT ts $ GEQ $ UTXO.Value $ fromIntegral campaignTarget)
    (blockHeightT $ fromIntegral <$> Interval campaignDeadline campaignCollectionDeadline)

refund :: (Monad m, WalletAPI m) => Campaign -> TxOutRef' -> UTXO.Value -> m ()
refund c ref val = do
    oo <- ownPubKeyTxOut val
    let scr = contributionScript c
        i   = scriptTxIn ref scr UTXO.unitRedeemer
    signAndSubmit (Set.singleton i) [oo]

-- | Collect all campaign funds (campaign owner)
--
--
collect :: (Monad m, WalletAPI m) => Campaign -> [(TxOutRef', UTXO.Value)] -> m ()
collect cmp contributions = do
    oo <- ownPubKeyTxOut value
    let scr        = contributionScript cmp
        con (r, _) = scriptTxIn r scr UTXO.unitRedeemer
        ins        = con <$> contributions
    signAndSubmit (Set.fromList ins) [oo]
    where
      value = getSum $ foldMap (Sum . snd) contributions

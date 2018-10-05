-- | Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction. This is, of course, limited by the maximum
-- number of inputs a transaction can have.
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Language.Plutus.Coordination.Contracts.CrowdFunding (
    -- * Campaign parameters
    Campaign(..)
    , CampaignPLC(..)
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

import           Control.Applicative                  (Applicative (..))
import           Control.Monad                        (Monad (..))
import           Control.Monad.Error.Class            (MonadError (..))
import qualified Data.Set                             as Set

import           Language.Plutus.Coordination.Plutus  (Height, PendingTx (..), PendingTxIn (..), PubKey (..), Value)
import qualified Language.Plutus.CoreToPLC.Primitives as Prim
import           Language.Plutus.TH                   (PlcCode, applyPlc, plutus)
import           Wallet.API                           (EventTrigger (..), Range (..), WalletAPI (..), WalletAPIError,
                                                       otherError, pubKey)
import           Wallet.UTXO                          (Address', DataScript (..), Tx (..), TxOutRef', Validator (..),
                                                       scriptTxIn, scriptTxOut)
import qualified Wallet.UTXO                          as UTXO

import           Prelude                              (Bool (..), Num (..), Ord (..), fromIntegral, succ, sum, ($),
                                                       (<$>))

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Height
    , campaignTarget             :: Value
    , campaignCollectionDeadline :: Height
    , campaignOwner              :: CampaignActor
    }

type CampaignActor = PubKey

-- | Value of type `Campaign` in PLC
newtype CampaignPLC = CampaignPLC PlcCode

-- | Contribute funds to the campaign (contributor)
--
contribute :: (MonadError WalletAPIError m, WalletAPI m) => CampaignPLC -> Value -> m ()
contribute c value = do
    _ <- if value <= 0 then otherError "Must contribute a positive value" else pure ()
    -- TODO: Uncomment when we can translate values to PLC. Until then, we use
    --       a constant `PubKey 1` for the data script
    -- contributorPubKey <- pubKey <$> myKeyPair

    -- TODO: Remove duplicate definition of Value
    --       (Value = Integer in Haskell land but Value = Int in PLC land)
    let v' = UTXO.Value $ fromIntegral value
    (payment, change) <- createPaymentWithChange v'
    let o = scriptTxOut v' (contributionScript c) d
        d = DataScript $(plutus [| PubKey 1 |])

    submitTxn Tx
      { txInputs  = payment
      , txOutputs = [o, change]
      , txForge = 0
      , txFee = 0
      }
    -- the transaction above really ought to be merely a transaction *template* and the transaction fee ought to be
    -- added by the Wallet API Plutus library on the basis of the size and other costs of the transaction

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
contributionScript :: CampaignPLC -> Validator
contributionScript (CampaignPLC c)  = Validator val where
    val = applyPlc inner c

    --   See note [Contracts and Validator Scripts] in
    --       Language.Plutus.Coordination.Contracts
    inner = $(plutus [| (\Campaign{..} () (a :: CampaignActor) (p :: PendingTx () CampaignActor) ->
        let
            -- | Check that a transaction input is signed by the private key of the given
            --   public key.
            signedBy :: PendingTxIn a -> CampaignActor -> Bool
            signedBy _ _ = True -- TODO: Actually check signature

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) l r = case (l, r) of
                (True, True) -> True
                _            -> False

            -- | Check that a pending transaction is signed by the private key
            --   of the given public key.
            signedByT :: PendingTx a b -> CampaignActor -> Bool
            signedByT _ _ = True -- TODO: Actually check signature

            PendingTx _ _ _ _ _ h = p

            isValid = case p of
                PendingTx (_, v1) ((_, v2):_) _ _ _ _ -> -- the "successful campaign" branch
                    let
                        pledgedFunds = v1 + v2

                        payToOwner = h > campaignDeadline &&
                                     h <= campaignCollectionDeadline &&
                                     pledgedFunds >= campaignTarget &&
                                     signedByT p campaignOwner
                    in payToOwner
                PendingTx (t, _) [] _ _ _ _ -> -- the "refund" branch
                    let
                        -- Check that a refund transaction only spends the
                        -- amount that was pledged by the contributor
                        -- identified by `a :: CampaignActor`
                        contributorOnly = signedBy t a
                        refundable   = h > campaignCollectionDeadline &&
                                       contributorOnly &&
                                       signedByT p a
                        -- In case of a refund, we can only collect the funds that
                        -- were committed by this contributor
                    in refundable
                _ -> False
        in
        if isValid then () else Prim.error ()) |])

-- | Given the campaign data and the output from the contributing transaction,
--   make a trigger that fires when the transaction can be refunded.
refundTrigger :: Campaign -> Address' -> EventTrigger
refundTrigger Campaign{..} t = And
    (FundsAtAddress [t]  (GEQ 1))
    (BlockHeightRange (GEQ $ fromIntegral $ succ campaignCollectionDeadline))

-- | Given the public key of the campaign owner, generate an event trigger that
-- fires when the funds can be collected.
collectFundsTrigger :: Campaign -> [Address'] -> EventTrigger
collectFundsTrigger Campaign{..} ts = And
    (FundsAtAddress ts $ GEQ $ UTXO.Value $ fromIntegral campaignTarget)
    (BlockHeightRange $ fromIntegral <$> Interval campaignDeadline campaignCollectionDeadline)

refund :: (Monad m, WalletAPI m) => CampaignPLC -> TxOutRef' -> UTXO.Value -> m ()
refund c ref val = do
    contributorPubKey <- pubKey <$> myKeyPair
    oo <- payToPublicKey val
    let scr = contributionScript c
        i   = scriptTxIn ref scr UTXO.unitRedeemer
    submitTxn Tx
        { txInputs = Set.singleton i
        , txOutputs = [oo]
        , txForge = 0
        , txFee = 0
        }

-- | Collect all campaign funds (campaign owner)
--
--
collect :: (Monad m, WalletAPI m) => CampaignPLC -> [(TxOutRef', PubKey, UTXO.Value)] -> m ()
collect cmp contributions = do
    oo <- payToPublicKey value
    contributorPubKey <- pubKey <$> myKeyPair
    let scr           = contributionScript cmp
        con (r, _, _) = scriptTxIn r scr UTXO.unitRedeemer
        ins           = con <$> contributions
    submitTxn Tx
        { txInputs  = Set.fromList ins
        , txOutputs = [oo]
        , txForge   = 0
        , txFee     = 0 -- TODO: Fee
        }
    where
      value = sum [ vl | (_, _, vl) <- contributions]

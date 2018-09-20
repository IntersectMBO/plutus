-- | Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction. This is, of course, limited by the maximum
-- number of inputs a transaction can have.
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Language.Plutus.Coordination.Contracts.CrowdFunding (
    Campaign(..)
    -- * Functionality for campaign contributors
    , contribute
    , contributionScript
    , refund
    , refundTrigger
    -- * Functionality for campaign owners
    , collect
    , collectFundsTrigger
    ) where

import           Language.Plutus.Coordination.Plutus
import           Language.Plutus.TH (plutusT)
import qualified Language.Plutus.CoreToPLC.Primitives as Prim

import           Prelude                              (Bool (..), Either (..), Num (..), Ord (..), succ, sum, ($))

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: !BlockHeight
    , campaignTarget             :: !Value
    , campaignCollectionDeadline :: !BlockHeight
    , campaignOwner              :: !PubKey
    }

-- | Contribute funds to the campaign (contributor)
--
contribute :: Campaign -> Value -> TxM [TxOutRef]
contribute c value = do
    assert (value > 0)
    contributorPubKey <- lookupMyPubKey
    myPayment         <- createPayment (value + standardTxFee)
    let validator = contributionScript c contributorPubKey
        o = TxOutScript
            value
            (hash validator)
            0 -- TODO: contributorPubKey ought to be lifted into PLC at coordination runtime as the data script
    submitTransaction Tx
      { txInputs  = Left myPayment -- TODO: Change to [myPayment] when we can have a list of inputs
      , txOutputs = Left o
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
contributionScript ::
       Campaign
    -> PubKey
    -> PlutusTx
contributionScript _ _  = PlutusTx inner where

    --   See note [Contracts and Validator Scripts] in
    --       Language.Plutus.Coordination.Contracts
    inner = $$(plutusT [|| (\() () p Campaign{..} contribPubKey ->
        let
            -- | Check that a transaction input is signed by the private key of the given
            --   public key.
            signedBy :: TxIn -> PubKey -> Bool
            signedBy = Prim.error

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = Prim.error

            -- | Check that a pending transaction is signed by the private key
            --   of the given public key.
            signedByT :: PendingTx -> PubKey -> Bool
            signedByT = Prim.error

            PendingTx pendingTxBlockHeight _ pendingTxTransaction = p

            isValid = case pendingTxTransaction of
                Tx (Right (t1, t2)) _ -> -- the "successful campaign" branch
                    let
                        TxIn (TxOutRef v1 _ _) _ _ _ = t1
                        TxIn (TxOutRef v2 _ _) _ _ _ = t2
                        pledgedFunds = v1 + v2

                        payToOwner = pendingTxBlockHeight > campaignDeadline &&
                                     pendingTxBlockHeight <= campaignCollectionDeadline &&
                                     pledgedFunds >= campaignTarget &&
                                     signedByT p campaignOwner
                    in payToOwner
                Tx (Left t) _ -> -- the "refund" branch
                    let
                        -- Check that a refund transaction only spends the
                        -- amount that was pledged by the contributor
                        -- identified by `contribPubKey`
                        contributorOnly = signedBy t contribPubKey
                        refundable   = pendingTxBlockHeight > campaignCollectionDeadline &&
                                       contributorOnly &&
                                       signedByT p contribPubKey
                        -- In case of a refund, we can only collect the funds that
                        -- were committed by this contributor
                    in refundable
        in
        if isValid then () else Prim.error) ||])

-- | Given the campaign data and the output from the contributing transaction,
--   make a trigger that fires when the transaction can be refunded.
refundTrigger :: Campaign -> Address -> EventTrigger
refundTrigger Campaign{..} t = And
    (FundsAtAddress [t]  (GEQ 1))
    (BlockHeightRange (GEQ $ succ campaignCollectionDeadline))

-- | Given the public key of the campaign owner, generate an event trigger that
-- fires when the funds can be collected.
collectFundsTrigger :: Campaign -> [Address] -> EventTrigger
collectFundsTrigger Campaign{..} ts = And
    (FundsAtAddress ts $ GEQ campaignTarget)
    (BlockHeightRange $ Interval campaignDeadline campaignCollectionDeadline)

refund :: Campaign -> TxOutRef -> TxM [TxOutRef]
refund c ref = do
    kp <- lookupMyKeyPair
    let scr = contributionScript c (pubKey kp)
        o = TxOutPubKey value (pubKey kp)
        i = txInSign ref scr unitPLC unitPLC kp
    submitTransaction $ Tx {
      txInputs = Left i,
      txOutputs = Left o
    } where
      value = txOutRefValue ref - standardTxFee -- TODO: Fee should be inserted by wallet

-- | Collect all campaign funds (campaign owner)
--
--
collect :: Campaign -> (TxOutRef, PubKey) -> (TxOutRef, PubKey) -> TxM [TxOutRef]
collect cmp (o1, ck1) (o2, ck2) = do
    ownerKeyPair <- lookupMyKeyPair
    let oo  = TxOutPubKey value (pubKey ownerKeyPair)
        scr = contributionScript cmp
    submitTransaction Tx
      { txInputs  = Right (
          txInSign o1 (scr ck1) unitPLC unitPLC ownerKeyPair,
          txInSign o2 (scr ck2) unitPLC unitPLC ownerKeyPair)
      , txOutputs = Left oo
      }
    where
      value = sum [txOutRefValue outRef | outRef <- [o1, o2]] + standardTxFee

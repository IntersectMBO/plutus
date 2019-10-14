{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
-- | An general-purpose escrow contract in Plutus
module Language.PlutusTx.Coordination.Contracts.Escrow(
    -- $escrow
    Escrow
    , EscrowParams(..)
    , EscrowTarget(..)
    , payToScriptTarget
    , payToPubKeyTarget
    , escrowAddress
    , escrowScript
    , targetValue
    , escrowContract
    -- * Actions
    , pay
    , payEp
    , redeem
    , redeemEp
    , refund
    , refundEp
    , RedeemFailReason(..)
    , RedeemResult(..)
    , RefundResult(..)
    , EscrowSchema
    ) where

import           Control.Applicative            (Applicative (..))
import           Control.Lens                   ((&), (^.), (.~), at, folded)
import           Control.Monad                  (void)
import qualified Data.Set                       as Set
import qualified Ledger
import           Ledger                         (Address, DataScript(..), PubKey, Slot, ValidatorHash, scriptOutputsAt,
                                                 txSignedBy, valuePaidTo, interval, TxId, ValidatorScript, TxOut, pubKeyTxOut, scriptTxOut')
import           Ledger.Interval                (after, before, from)
import qualified Ledger.Interval                as Interval
import           Ledger.AddressMap              (values)
import qualified Ledger.Typed.Scripts           as Scripts
import qualified Ledger.Scripts                 as Scripts
import           Ledger.Validation              (PendingTx, PendingTx' (..))
import           Ledger.Value                   (Value, lt, geq)

import qualified Language.Plutus.Contract.Typed.Tx as Typed
import           Language.Plutus.Contract
import qualified Language.PlutusTx              as PlutusTx
import           Language.PlutusTx.Prelude      hiding (Applicative (..), check)

import qualified Prelude                        as Haskell

type EscrowSchema =
    BlockchainActions
        .\/ Endpoint "pay-escrow" (PubKey, Value)
        .\/ Endpoint "redeem-escrow" ()
        .\/ Endpoint "refund-escrow" ()

-- $escrow
-- The escrow contract implements the exchange of value between multiple 
-- parties. It is defined by a list of targets (public keys and script 
-- addresses, each associated with a value). It works similar to the 
-- crowdfunding contract in that the contributions can be made independently,
-- and the funds can be unlocked only by a transaction that pays the correct
-- amount to each target. A refund is possible if the outputs locked by the 
-- contract have not been spent by the deadline. (Compared to the crowdfunding
-- contract, the refund policy is simpler because here because there is no
-- "collection period" during which the outputs may be spent after the deadline
-- has passed. This is because we're assuming that the participants in the 
-- escrow contract will make their deposits as quickly as possible after 
-- agreeing on a deal)
-- 
-- The contract supports two modes of operation, manual and automatic. In 
-- manual mode, all actions are driven by endpoints that exposed via 'payEp'
-- 'redeemEp' and 'refundEp'. In automatic mode, the 'pay', 'redeem' and 
-- 'refund'actions start immediately. This mode is useful when the escrow is 
-- called from within another contract, for example during setup (collection of
-- the initial deposits).

-- | Defines where the money should go.
data EscrowTarget =
    PubKeyTarget PubKey Value
    | ScriptTarget ValidatorHash DataScript Value

PlutusTx.makeLift ''EscrowTarget

-- | An 'EscrowTarget' that pays the value to a public key address.
payToPubKeyTarget :: PubKey -> Value -> EscrowTarget
payToPubKeyTarget = PubKeyTarget

-- | An 'EscrowTarget' that pays the value to a script address, with the
--   given data script.
payToScriptTarget :: Address -> DataScript -> Value -> EscrowTarget
payToScriptTarget (Ledger.AddressOf hsh) = ScriptTarget (Scripts.plcValidatorDigest hsh)

-- | Definition of an escrow contract, consisting of a deadline and a list of targets
data EscrowParams =
    EscrowParams
        { escrowDeadline :: Slot
        -- ^ Latest point at which the outputs may be spent.
        , escrowTargets  :: [EscrowTarget]
        -- ^ Where the money should go. For each target, the contract checks that
        --   the output 'mkTxOutput' of the target is present in the spending
        --   transaction.
        }

PlutusTx.makeLift ''EscrowParams

-- | The total 'Value' that must be paid into the escrow contract
--   before it can be unlocked
targetValue :: EscrowParams -> Value
targetValue = foldl (\vl tgt -> vl + targetVal tgt) mempty . escrowTargets where
    targetVal = \case
        PubKeyTarget _ vl -> vl
        ScriptTarget _ _ vl -> vl

-- | Create a 'Ledger.TxOut' value for the target
mkTxOutput :: EscrowTarget -> TxOut
mkTxOutput = \case
    PubKeyTarget pk vl -> pubKeyTxOut vl pk
    ScriptTarget hsh ds vl -> scriptTxOut' vl (Ledger.AddressOf (Scripts.unsafePlcAddress hsh)) ds


data Action = Redeem | Refund

PlutusTx.makeIsData ''Action
PlutusTx.makeLift ''Action

{-# INLINABLE meetsTarget #-}
meetsTarget :: PendingTx -> EscrowTarget -> Bool
meetsTarget ptx = \case
    PubKeyTarget pk vl ->
        valuePaidTo ptx pk `geq` vl
    ScriptTarget validatorHash dataScript vl ->
        case scriptOutputsAt validatorHash ptx of
            [(dataScript', vl')] -> dataScript' == dataScript && vl' `geq` vl
            _ -> False

{-# INLINABLE validate #-}
validate :: EscrowParams -> PubKey -> Action -> PendingTx -> Bool
validate EscrowParams{escrowDeadline, escrowTargets} contributor action ptx@PendingTx{pendingTxValidRange} =
    case action of
        Redeem ->
            traceIfFalseH "escrowDeadline-after" (escrowDeadline `after` pendingTxValidRange)
            && traceIfFalseH "meetsTarget" (all (meetsTarget ptx) escrowTargets)
        Refund ->
            traceIfFalseH "escrowDeadline-before" (escrowDeadline `before` pendingTxValidRange)
            && traceIfFalseH "txSignedBy" (ptx `txSignedBy` contributor)

data Escrow
instance Scripts.ScriptType Escrow where
    type instance RedeemerType Escrow = Action
    type instance DataType Escrow = PubKey

escrowScript :: EscrowParams -> ValidatorScript
escrowScript = Scripts.validatorScript . scriptInstance

scriptInstance :: EscrowParams -> Scripts.ScriptInstance Escrow
scriptInstance escrow = Scripts.Validator @Escrow
    ($$(PlutusTx.compile [|| validate ||]) `PlutusTx.applyCode` PlutusTx.liftCode escrow)
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @PubKey @Action

-- | The address of an escrow contract
escrowAddress :: EscrowParams -> Ledger.Address
escrowAddress = Scripts.scriptAddress . scriptInstance

escrowContract :: EscrowParams -> Contract EscrowSchema ()
escrowContract escrow = 
    let payAndRefund = do
            (ownPubKey, vl) <- endpoint @"pay-escrow"
            _ <- pay escrow ownPubKey vl
            _ <- awaitSlot (escrowDeadline escrow)
            refund escrow ownPubKey
    in void payAndRefund <|> void (redeemEp escrow)

-- | 'pay' with an endpoint that gets the owner's public key and the
--   contribution.
payEp
    ::
    ( HasWriteTx s
    , HasEndpoint "pay-escrow" (PubKey, Value) s
    )
    => EscrowParams
    -> Contract s TxId
payEp escrow = do
    (ownPubKey, vl) <- endpoint @"pay-escrow"
    pay escrow ownPubKey vl

-- | Pay some money into the escrow contract.
pay 
    :: HasWriteTx s
    => EscrowParams
    -- ^ The escrow contract
    -> PubKey
    -- ^ Public key of the contributor (used for refunds)
    -> Value
    -- ^ How much money to pay in
    -> Contract s TxId
pay escrow ownPubKey vl = do
    let ds = DataScript (PlutusTx.toData ownPubKey)
        tx = payToScript vl (escrowAddress escrow) ds
                & validityRange .~ Ledger.interval 1 (escrowDeadline escrow)
    writeTxSuccess tx

data RedeemFailReason = DeadlinePassed | NotEnoughFundsAtAddress
  deriving (Haskell.Eq, Show)

data RedeemResult =
    RedeemSuccess TxId
    | RedeemFail RedeemFailReason
    deriving (Haskell.Eq, Show)

-- | 'redeem' with an endpoint.
redeemEp 
    :: 
    ( HasUtxoAt s 
    , HasAwaitSlot s
    , HasWriteTx s
    , HasEndpoint "redeem-escrow" () s
    )
    => EscrowParams
    -> Contract s RedeemResult
redeemEp escrow = endpoint @"redeem-escrow" >> redeem escrow

-- | Redeem all outputs at the contract address using a transaction that
--   has all the outputs defined in the contract's list of targets.
redeem 
    :: 
    ( HasUtxoAt s 
    , HasAwaitSlot s
    , HasWriteTx s
    )
    => EscrowParams
    -> Contract s RedeemResult
redeem escrow = do
    currentSlot <- awaitSlot 0
    unspentOutputs <- utxoAt (escrowAddress escrow)
    let addr = escrowAddress escrow
        valRange = 
            let itvl = Interval.from 1
                upperBound = Interval.strictUpperBound (escrowDeadline escrow)
            in itvl { Interval.ivTo = upperBound }
        tx = Typed.collectFromScriptFilter (\_ _ -> True) unspentOutputs (scriptInstance escrow) Redeem
            & validityRange .~ valRange
            & outputs .~ fmap mkTxOutput (escrowTargets escrow)
    if currentSlot >= escrowDeadline escrow
    then pure $ RedeemFail DeadlinePassed
    else if (values unspentOutputs ^. at addr . folded) `lt` targetValue escrow
         then pure $ RedeemFail NotEnoughFundsAtAddress
         else RedeemSuccess <$> writeTxSuccess tx

data RefundResult = RefundOK TxId | RefundFailed 
    deriving (Haskell.Eq, Show)

-- | 'refund' with an endpoint.
refundEp 
    :: 
    ( HasUtxoAt s 
    , HasWriteTx s
    , HasEndpoint "refund-escrow" () s
    )
    => EscrowParams
    -> PubKey
    -> Contract s RefundResult
refundEp escrow txid = endpoint @"refund-escrow" >> refund escrow txid

-- | Claim a refund of the contribution.
refund 
    :: ( HasUtxoAt s
       , HasWriteTx s )
    => EscrowParams 
    -> PubKey
    -> Contract s RefundResult
refund escrow pk = do
    unspentOutputs <- utxoAt (escrowAddress escrow)
    let flt _ txOut = Ledger.txOutData txOut == Just (DataScript (PlutusTx.toData pk))
        tx' = Typed.collectFromScriptFilter flt unspentOutputs (scriptInstance escrow) Refund
                & validityRange .~ from (succ $ escrowDeadline escrow)
    if not . Set.null $ tx' ^. inputs
    then RefundOK <$> writeTxSuccess tx'
    else pure $ RefundFailed

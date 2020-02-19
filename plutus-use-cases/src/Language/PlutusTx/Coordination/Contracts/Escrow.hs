{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
-- | A general-purpose escrow contract in Plutus
module Language.PlutusTx.Coordination.Contracts.Escrow(
    -- $escrow
    Escrow
    , EscrowError(..)
    , AsEscrowError(..)
    , EscrowParams(..)
    , EscrowTarget(..)
    , payToScriptTarget
    , payToPubKeyTarget
    , targetTotal
    , escrowContract
    , payRedeemRefund
    , scriptInstance
    -- * Actions
    , pay
    , payEp
    , redeem
    , redeemEp
    , refund
    , refundEp
    , RedeemFailReason(..)
    , RedeemSuccess(..)
    , RefundSuccess(..)
    , EscrowSchema
    ) where

import           Control.Lens                   ((^.), at, folded, prism', makeClassyPrisms)
import           Control.Monad                  (void)
import           Control.Monad.Error.Lens       (throwing)
import qualified Ledger
import           Ledger                         (DataValue(..), PubKeyHash, Slot, ValidatorHash, DataValueHash, scriptOutputsAt,
                                                 txSignedBy, valuePaidTo, interval, TxId, TxOutTx (..))
import           Ledger.Interval                (after, before, from)
import qualified Ledger.Interval                as Interval
import           Ledger.AddressMap              (values)
import qualified Ledger.Typed.Scripts           as Scripts
import           Ledger.Typed.Scripts           (ScriptInstance)
import           Ledger.Validation              (PendingTx, PendingTx' (..))
import           Ledger.Value                   (Value, lt, geq)

import qualified Language.Plutus.Contract.Typed.Tx as Typed
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Tx    as Tx
import qualified Language.PlutusTx              as PlutusTx
import           Language.PlutusTx.Prelude      hiding (Applicative (..), Semigroup(..), check, foldMap)

import qualified Prelude                        as Haskell
import           Prelude                        (Semigroup(..), foldMap)

type EscrowSchema =
    BlockchainActions
        .\/ Endpoint "pay-escrow" Value
        .\/ Endpoint "redeem-escrow" ()
        .\/ Endpoint "refund-escrow" ()

data RedeemFailReason = DeadlinePassed | NotEnoughFundsAtAddress
    deriving (Haskell.Eq, Show)

data EscrowError =
    RedeemFailed RedeemFailReason
    | RefundFailed
    | OtherEscrowError ContractError
    deriving Show

instance AsContractError EscrowError where
    _ContractError = prism' OtherEscrowError (\case { OtherEscrowError e -> Just e; _ -> Nothing})

makeClassyPrisms ''EscrowError
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

-- | Defines where the money should go. Usually we have `d = DataValue` (when
--   defining `EscrowTarget` values in off-chain code). Sometimes we have
--   `d = DataValueHash` (when checking the hashes in on-chain code)
data EscrowTarget d =
    PubKeyTarget PubKeyHash Value
    | ScriptTarget ValidatorHash d Value
    deriving (Haskell.Functor)

PlutusTx.makeLift ''EscrowTarget

-- | An 'EscrowTarget' that pays the value to a public key address.
payToPubKeyTarget :: PubKeyHash -> Value -> EscrowTarget d
payToPubKeyTarget = PubKeyTarget

-- | An 'EscrowTarget' that pays the value to a script address, with the
--   given data script.
payToScriptTarget :: ValidatorHash -> DataValue -> Value -> EscrowTarget DataValue
payToScriptTarget = ScriptTarget

-- | Definition of an escrow contract, consisting of a deadline and a list of targets
data EscrowParams d =
    EscrowParams
        { escrowDeadline :: Slot
        -- ^ Latest point at which the outputs may be spent.
        , escrowTargets  :: [EscrowTarget d]
        -- ^ Where the money should go. For each target, the contract checks that
        --   the output 'mkTxOutput' of the target is present in the spending
        --   transaction.
        } deriving (Haskell.Functor)

PlutusTx.makeLift ''EscrowParams

-- | The total 'Value' that must be paid into the escrow contract
--   before it can be unlocked
targetTotal :: EscrowParams d -> Value
targetTotal = foldl (\vl tgt -> vl + targetValue tgt) mempty . escrowTargets

-- | The 'Value' specified by an 'EscrowTarget'
targetValue :: EscrowTarget d -> Value
targetValue = \case
    PubKeyTarget _ vl -> vl
    ScriptTarget _ _ vl -> vl

-- | Create a 'Ledger.TxOut' value for the target
mkTx :: EscrowTarget DataValue -> UnbalancedTx
mkTx = \case
    PubKeyTarget pkh vl ->
        Tx.payToPubKeyHash vl pkh
    ScriptTarget vs ds vl ->
        Tx.payToScript
            vl
            (Ledger.scriptHashAddress vs)
            ds

data Action = Redeem | Refund

PlutusTx.makeIsData ''Action
PlutusTx.makeLift ''Action

{-# INLINABLE meetsTarget #-}
-- | @ptx `meetsTarget` tgt@ if @ptx@ pays at least @targetValue tgt@ to the
--   target address.
--
--   The reason why this does not require the target amount to be equal
--   to the actual amount is to enable any excess funds consumed by the
--   spending transaction to be paid to target addresses. This may happen if
--   the target address is also used as a change address for the spending
--   transaction, and allowing the target to be exceed prevents outsiders from
--   poisoning the contract by adding arbitrary outputs to the script address.
meetsTarget :: PendingTx -> EscrowTarget DataValueHash -> Bool
meetsTarget ptx = \case
    PubKeyTarget pkh vl ->
        valuePaidTo ptx pkh `geq` vl
    ScriptTarget validatorHash dataValue vl ->
        case scriptOutputsAt validatorHash ptx of
            [(dataValue', vl')] ->
                traceIfFalseH "dataValue" (dataValue' == dataValue)
                && traceIfFalseH "value" (vl' `geq` vl)
            _ -> False

{-# INLINABLE validate #-}
validate :: EscrowParams DataValueHash -> PubKeyHash -> Action -> PendingTx -> Bool
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
    type instance DataType Escrow = PubKeyHash

scriptInstance :: EscrowParams DataValue -> Scripts.ScriptInstance Escrow
scriptInstance escrow = go (Haskell.fmap Ledger.dataValueHash escrow) where
    go escrow' =
        Scripts.validator @Escrow
            ($$(PlutusTx.compile [|| validate ||]) `PlutusTx.applyCode` PlutusTx.liftCode escrow')
            $$(PlutusTx.compile [|| wrap ||])
    wrap = Scripts.wrapValidator @PubKeyHash @Action

escrowContract
    :: (AsEscrowError e, AsContractError e)
    => EscrowParams DataValue
    -> Contract EscrowSchema e ()
escrowContract escrow =
    let inst = scriptInstance escrow
        payAndRefund = do
            vl <- endpoint @"pay-escrow"
            _ <- pay inst escrow vl
            _ <- awaitSlot (escrowDeadline escrow)
            refund inst escrow
    in void payAndRefund <|> void (redeemEp escrow)

-- | 'pay' with an endpoint that gets the owner's public key and the
--   contribution.
payEp
    ::
    ( HasWriteTx s
    , HasOwnPubKey s
    , HasEndpoint "pay-escrow" Value s
    , AsContractError e
    )
    => EscrowParams DataValue
    -> Contract s e TxId
payEp escrow = do
    vl <- endpoint @"pay-escrow"
    pay (scriptInstance escrow) escrow vl

-- | Pay some money into the escrow contract.
pay
    :: ( HasWriteTx s
       , HasOwnPubKey s
       , AsContractError e
       )
    => ScriptInstance Escrow
    -- ^ The instance
    -> EscrowParams DataValue
    -- ^ The escrow contract
    -> Value
    -- ^ How much money to pay in
    -> Contract s e TxId
pay inst escrow vl = do
    pk <- ownPubKey
    let ds = DataValue (PlutusTx.toData $ Ledger.pubKeyHash pk)
        tx = payToScript vl (Scripts.scriptAddress inst) ds
                <> mustBeValidIn (Ledger.interval 1 (escrowDeadline escrow))
    submitTx tx

newtype RedeemSuccess = RedeemSuccess TxId
    deriving (Haskell.Eq, Show)

-- | 'redeem' with an endpoint.
redeemEp
    ::
    ( HasUtxoAt s
    , HasAwaitSlot s
    , HasWriteTx s
    , HasEndpoint "redeem-escrow" () s
    , AsEscrowError e
    , AsContractError e
    )
    => EscrowParams DataValue
    -> Contract s e RedeemSuccess
redeemEp escrow = endpoint @"redeem-escrow" >> redeem (scriptInstance escrow) escrow

-- | Redeem all outputs at the contract address using a transaction that
--   has all the outputs defined in the contract's list of targets.
redeem
    ::
    ( HasUtxoAt s
    , HasAwaitSlot s
    , HasWriteTx s
    , AsEscrowError e
    , AsContractError e
    )
    => ScriptInstance Escrow
    -> EscrowParams DataValue
    -> Contract s e RedeemSuccess
redeem inst escrow = do
    let addr = Scripts.scriptAddress inst
    currentSlot <- awaitSlot 0
    unspentOutputs <- utxoAt addr
    let
        valRange = Interval.to (pred $ escrowDeadline escrow)
        tx = Typed.collectFromScript unspentOutputs (scriptInstance escrow) Redeem
                <> foldMap mkTx (escrowTargets escrow)
                <> mustBeValidIn valRange
    if currentSlot >= escrowDeadline escrow
    then throwing _RedeemFailed DeadlinePassed
    else if (values unspentOutputs ^. at addr . folded) `lt` targetTotal escrow
         then throwing _RedeemFailed NotEnoughFundsAtAddress
         else RedeemSuccess <$> submitTx tx

newtype RefundSuccess = RefundSuccess TxId
    deriving (Haskell.Eq, Show)

-- | 'refund' with an endpoint.
refundEp
    ::
    ( HasUtxoAt s
    , HasWriteTx s
    , HasOwnPubKey s
    , HasEndpoint "refund-escrow" () s
    , AsEscrowError e
    , AsContractError e
    )
    => EscrowParams DataValue
    -> Contract s e RefundSuccess
refundEp escrow = endpoint @"refund-escrow" >> refund (scriptInstance escrow) escrow

-- | Claim a refund of the contribution.
refund
    :: ( HasUtxoAt s
       , HasOwnPubKey s
       , AsEscrowError e
       , AsContractError e
       , HasWriteTx s)
    => ScriptInstance Escrow
    -> EscrowParams DataValue
    -> Contract s e RefundSuccess
refund inst escrow = do
    pk <- ownPubKey
    unspentOutputs <- utxoAt (Scripts.scriptAddress inst)
    let flt _ (TxOutTx _ txOut) = Ledger.txOutData txOut == (Just $ Ledger.dataValueHash $ DataValue $ PlutusTx.toData $ Ledger.pubKeyHash pk)
        tx' = Typed.collectFromScriptFilter flt unspentOutputs (scriptInstance escrow) Refund
                <> mustBeValidIn (from (succ $ escrowDeadline escrow))
    if modifiesUtxoSet tx'
    then RefundSuccess <$> submitTx tx'
    else throwing _RefundFailed ()

-- | Pay some money into the escrow contract. Then release all funds to their
--   specified targets if enough funds were deposited before the deadline,
--   or reclaim the contribution if the goal has not been met.
payRedeemRefund
    :: ( HasUtxoAt s
       , HasWatchAddress s
       , HasWriteTx s
       , HasAwaitSlot s
       , HasOwnPubKey s
       , AsEscrowError e
       , AsContractError e
       )
    => EscrowParams DataValue
    -> Value
    -> Contract s e (Either RefundSuccess RedeemSuccess)
payRedeemRefund params vl = do
    let inst = scriptInstance params
    -- Pay the value 'vl' into the contract and, at the same time, wait
    -- for the 'targetTotal' of the contract to appear at the address, or
    -- for the 'escrowDeadline' to pass, whichever happens first.
    (_, outcome) <- both
                        (pay inst params vl)
                        (awaitSlot (escrowDeadline params) `selectEither` fundsAtAddressGeq (Scripts.scriptAddress inst) (targetTotal params))
    -- If 'outcome' is a 'Right' then the total amount was deposited before the
    -- deadline, and we procedd with 'redeem'. If it's a 'Left', there are not
    -- enough funds at the address and we refund our own contribution.
    case outcome of
        Right _ -> Right <$> redeem inst params
        Left _ -> Left <$> refund inst params

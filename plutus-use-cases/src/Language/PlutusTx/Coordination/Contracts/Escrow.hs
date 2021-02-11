{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
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

import           Control.Lens                      (makeClassyPrisms, review)
import           Control.Monad                     (void)
import           Control.Monad.Error.Lens          (throwing)
import           Data.Aeson                        (FromJSON, ToJSON)
import           GHC.Generics                      (Generic)

import           Ledger                            (Datum (..), DatumHash, PubKeyHash, Slot, TxId, TxOutTx (..),
                                                    ValidatorHash, interval, scriptOutputsAt, txId, txSignedBy,
                                                    valuePaidTo)
import qualified Ledger
import           Ledger.Constraints                (TxConstraints)
import qualified Ledger.Constraints                as Constraints
import           Ledger.Contexts                   (TxInfo (..), ValidatorCtx (..))
import           Ledger.Interval                   (after, before, from)
import qualified Ledger.Interval                   as Interval
import qualified Ledger.Tx                         as Tx
import           Ledger.Typed.Scripts              (ScriptInstance)
import qualified Ledger.Typed.Scripts              as Scripts
import           Ledger.Value                      (Value, geq, lt)

import           Language.Plutus.Contract
import qualified Language.Plutus.Contract.Typed.Tx as Typed
import qualified Language.PlutusTx                 as PlutusTx
import           Language.PlutusTx.Prelude         hiding (Applicative (..), Semigroup (..), check, foldMap)

import           Prelude                           (Semigroup (..), foldMap)
import qualified Prelude                           as Haskell

type EscrowSchema =
    BlockchainActions
        .\/ Endpoint "pay-escrow" Value
        .\/ Endpoint "redeem-escrow" ()
        .\/ Endpoint "refund-escrow" ()

data RedeemFailReason = DeadlinePassed | NotEnoughFundsAtAddress
    deriving stock (Haskell.Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data EscrowError =
    RedeemFailed RedeemFailReason
    | RefundFailed
    | EContractError ContractError
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''EscrowError

instance AsContractError EscrowError where
    _ContractError = _EContractError

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

-- | Defines where the money should go. Usually we have `d = Datum` (when
--   defining `EscrowTarget` values in off-chain code). Sometimes we have
--   `d = DatumHash` (when checking the hashes in on-chain code)
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
payToScriptTarget :: ValidatorHash -> Datum -> Value -> EscrowTarget Datum
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
    PubKeyTarget _ vl   -> vl
    ScriptTarget _ _ vl -> vl

-- | Create a 'Ledger.TxOut' value for the target
mkTx :: EscrowTarget Datum -> TxConstraints Action PubKeyHash
mkTx = \case
    PubKeyTarget pkh vl ->
        Constraints.mustPayToPubKey pkh vl
    ScriptTarget vs ds vl ->
        Constraints.mustPayToOtherScript vs ds vl

data Action = Redeem | Refund

data Escrow
instance Scripts.ScriptType Escrow where
    type instance RedeemerType Escrow = Action
    type instance DatumType Escrow = PubKeyHash

PlutusTx.unstableMakeIsData ''Action
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
meetsTarget :: TxInfo -> EscrowTarget DatumHash -> Bool
meetsTarget ptx = \case
    PubKeyTarget pkh vl ->
        valuePaidTo ptx pkh `geq` vl
    ScriptTarget validatorHash dataValue vl ->
        case scriptOutputsAt validatorHash ptx of
            [(dataValue', vl')] ->
                traceIfFalse "dataValue" (dataValue' == dataValue)
                && traceIfFalse "value" (vl' `geq` vl)
            _ -> False

{-# INLINABLE validate #-}
validate :: EscrowParams DatumHash -> PubKeyHash -> Action -> ValidatorCtx -> Bool
validate EscrowParams{escrowDeadline, escrowTargets} contributor action ValidatorCtx{valCtxTxInfo} =
    case action of
        Redeem ->
            traceIfFalse "escrowDeadline-after" (escrowDeadline `after` txInfoValidRange valCtxTxInfo)
            && traceIfFalse "meetsTarget" (all (meetsTarget valCtxTxInfo) escrowTargets)
        Refund ->
            traceIfFalse "escrowDeadline-before" (escrowDeadline `before` txInfoValidRange valCtxTxInfo)
            && traceIfFalse "txSignedBy" (valCtxTxInfo `txSignedBy` contributor)

scriptInstance :: EscrowParams Datum -> Scripts.ScriptInstance Escrow
scriptInstance escrow = go (Haskell.fmap Ledger.datumHash escrow) where
    go escrow' =
        Scripts.validator @Escrow
            ($$(PlutusTx.compile [|| validate ||]) `PlutusTx.applyCode` PlutusTx.liftCode escrow')
            $$(PlutusTx.compile [|| wrap ||])
    wrap = Scripts.wrapValidator @PubKeyHash @Action

escrowContract
    :: EscrowParams Datum
    -> Contract EscrowSchema EscrowError ()
escrowContract escrow =
    let inst = scriptInstance escrow
        payAndRefund = do
            vl <- endpoint @"pay-escrow"
            _ <- pay inst escrow vl
            _ <- awaitSlot (escrowDeadline escrow)
            refund inst escrow
    in void payAndRefund `select` void (redeemEp escrow)

-- | 'pay' with an endpoint that gets the owner's public key and the
--   contribution.
payEp
    ::
    ( HasWriteTx s
    , HasOwnPubKey s
    , HasEndpoint "pay-escrow" Value s
    , AsEscrowError e
    )
    => EscrowParams Datum
    -> Contract s e TxId
payEp escrow = do
    vl <- mapError (review _EContractError) (endpoint @"pay-escrow")
    pay (scriptInstance escrow) escrow vl

-- | Pay some money into the escrow contract.
pay
    :: ( HasWriteTx s
       , HasOwnPubKey s
       , AsEscrowError e
       )
    => ScriptInstance Escrow
    -- ^ The instance
    -> EscrowParams Datum
    -- ^ The escrow contract
    -> Value
    -- ^ How much money to pay in
    -> Contract s e TxId
pay inst escrow vl = mapError (review _EContractError) $ do
    pk <- ownPubKey
    let tx = Constraints.mustPayToTheScript (Ledger.pubKeyHash pk) vl
                <> Constraints.mustValidateIn (Ledger.interval 1 (escrowDeadline escrow))
    txId <$> submitTxConstraints inst tx

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
    )
    => EscrowParams Datum
    -> Contract s e RedeemSuccess
redeemEp escrow =
    mapError (review _EscrowError) $
    endpoint @"redeem-escrow" >> redeem (scriptInstance escrow) escrow

-- | Redeem all outputs at the contract address using a transaction that
--   has all the outputs defined in the contract's list of targets.
redeem
    ::
    ( HasUtxoAt s
    , HasAwaitSlot s
    , HasWriteTx s
    , AsEscrowError e
    )
    => ScriptInstance Escrow
    -> EscrowParams Datum
    -> Contract s e RedeemSuccess
redeem inst escrow = mapError (review _EscrowError) $ do
    let addr = Scripts.scriptAddress inst
    current <- currentSlot
    unspentOutputs <- utxoAt addr
    let
        valRange = Interval.to (pred $ escrowDeadline escrow)
        tx = Typed.collectFromScript unspentOutputs Redeem
                <> foldMap mkTx (escrowTargets escrow)
                <> Constraints.mustValidateIn valRange
    if current >= escrowDeadline escrow
    then throwing _RedeemFailed DeadlinePassed
    else if (foldMap (Tx.txOutValue . Tx.txOutTxOut) unspentOutputs) `lt` targetTotal escrow
         then throwing _RedeemFailed NotEnoughFundsAtAddress
         else RedeemSuccess . txId <$> submitTxConstraintsSpending inst unspentOutputs tx

newtype RefundSuccess = RefundSuccess TxId
    deriving newtype (Haskell.Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | 'refund' with an endpoint.
refundEp
    ::
    ( HasUtxoAt s
    , HasWriteTx s
    , HasOwnPubKey s
    , HasEndpoint "refund-escrow" () s
    )
    => EscrowParams Datum
    -> Contract s EscrowError RefundSuccess
refundEp escrow = endpoint @"refund-escrow" >> refund (scriptInstance escrow) escrow

-- | Claim a refund of the contribution.
refund
    :: ( HasUtxoAt s
       , HasOwnPubKey s
       , HasWriteTx s)
    => ScriptInstance Escrow
    -> EscrowParams Datum
    -> Contract s EscrowError RefundSuccess
refund inst escrow = do
    pk <- ownPubKey
    unspentOutputs <- utxoAt (Scripts.scriptAddress inst)
    let flt _ (TxOutTx _ txOut) = Ledger.txOutDatum txOut == Just (Ledger.datumHash $ Datum (PlutusTx.toData $ Ledger.pubKeyHash pk))
        tx' = Typed.collectFromScriptFilter flt unspentOutputs Refund
                <> Constraints.mustValidateIn (from (succ $ escrowDeadline escrow))
    if Constraints.modifiesUtxoSet tx'
    then RefundSuccess . txId <$> submitTxConstraintsSpending inst unspentOutputs tx'
    else throwing _RefundFailed ()

-- | Pay some money into the escrow contract. Then release all funds to their
--   specified targets if enough funds were deposited before the deadline,
--   or reclaim the contribution if the goal has not been met.
payRedeemRefund
    :: ( HasUtxoAt s
       , HasWriteTx s
       , HasAwaitSlot s
       , HasOwnPubKey s
       )
    => EscrowParams Datum
    -> Value
    -> Contract s EscrowError (Either RefundSuccess RedeemSuccess)
payRedeemRefund params vl = do
    let inst = scriptInstance params
    -- Pay the value 'vl' into the contract
    _ <- pay inst params vl
    outcome <- selectEither (awaitSlot (escrowDeadline params)) (fundsAtAddressGeq (Scripts.scriptAddress inst) (targetTotal params))
    -- wait
    -- for the 'targetTotal' of the contract to appear at the address, or
    -- for the 'escrowDeadline' to pass, whichever happens first.
    -- If 'outcome' is a 'Right' then the total amount was deposited before the
    -- deadline, and we procedd with 'redeem'. If it's a 'Left', there are not
    -- enough funds at the address and we refund our own contribution.
    case outcome of
        Right _ -> Right <$> redeem inst params
        Left _  -> Left <$> refund inst params

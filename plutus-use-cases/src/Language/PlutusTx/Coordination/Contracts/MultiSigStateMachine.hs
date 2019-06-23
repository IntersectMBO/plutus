{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | A multisig contract written as a state machine.
--   $multisig
module Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine(
      Params(..)
    , Payment(..)
    , State
    , validator
    , initialise
    , lock
    , proposePayment
    , cancelPayment
    , addSignature
    , makePayment
    ) where

import           Data.Foldable                (foldMap)
import qualified Data.Set                     as Set
import           Ledger                       (DataScript(..), RedeemerScript(..), ValidatorScript(..))
import qualified Ledger
import qualified Ledger.Slot                  as Slot
import           Ledger.Validation            (PendingTx(..))
import qualified Ledger.Validation            as Validation
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import           Wallet
import qualified Wallet                       as WAPI

import           Language.PlutusTx.Prelude
import           Language.PlutusTx.StateMachine (StateMachine(..))
import qualified Language.PlutusTx.StateMachine as SM

import           Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine.Types

--   $multisig
--   The n-out-of-m multisig contract works like a joint account of
--   m people, requiring the consent of n people for any payments.
--   In the smart contract the signatories are represented by public keys,
--   and approval takes the form of signatures on transactions.
--
--   The multisig contract in
--   'Language.PlutusTx.Coordination.Contracts.MultiSig' expects n signatures on
--   a single transaction. This requires an off-chain communication channel. The
--   multisig contract implemented in this module uses a proposal system that
--   allows participants to propose payments and attach their signatures to
--   proposals over a period of time, using separate transactions. All contract
--   state is kept on the chain so there is no need for off-chain communication.


-- | Check if a public key is one of the signatories of the multisig contract.
isSignatory :: PubKey -> Params -> Bool
isSignatory pk (Params sigs _) = any (\pk' -> pk == pk') sigs

-- | Check whether a list of public keys contains a given key.
containsPk :: PubKey -> [PubKey] -> Bool
containsPk pk = any (\pk' -> pk' == pk)

-- | Check whether a proposed 'Payment' is valid given the total
--   amount of funds currently locked in the contract.
isValidProposal :: Value -> Payment -> Bool
isValidProposal vl (Payment amt _ _) = amt `Value.leq` vl

-- | Check whether a proposed 'Payment' has expired.
proposalExpired :: PendingTx -> Payment -> Bool
proposalExpired (PendingTx _ _ _ _ _ rng _ _) (Payment _ _ ddl) = Slot.before ddl rng

-- | Check whether enough signatories (represented as a list of public keys)
--   have signed a proposed payment.
proposalAccepted :: Params -> [PubKey] -> Bool
proposalAccepted (Params signatories numReq) pks =
    let numSigned = length (filter (\pk -> containsPk pk pks) signatories)
    in numSigned >= numReq

-- | @valuePreserved v p@ is true if the pending transaction @p@ pays the amount
--   @v@ to a single pay-to-script output at this script's address.
valuePreserved :: Value -> PendingTx -> Bool
valuePreserved vl ptx =
    let ownHash = Validation.ownHash ptx
        numOutputs = length (Validation.scriptOutputsAt ownHash ptx)
        valueLocked = Validation.valueLockedBy ptx ownHash
    in 1 == numOutputs && valueLocked == vl

-- | @valuePaid pm ptx@ is true if the pending transaction @ptx@ pays
--   the amount specified in @pm@ to the public key address specified in @pm@
valuePaid :: Payment -> PendingTx -> Bool
valuePaid (Payment vl pk _) ptx = vl == (Validation.valuePaidTo ptx pk)

-- | @step params state input@ computes the next state given current state
--   @state@ and the input.
--   'step' does not perform any checks of the preconditions. This is done in
--   'stepWithChecks' below.
step :: State -> Input -> State
step s i = case (s, i) of
    (InitialState vl, ProposePayment pmt) ->
        CollectingSignatures vl pmt []
    (CollectingSignatures vl pmt pks, AddSignature pk) ->
        CollectingSignatures vl pmt (pk:pks)
    (CollectingSignatures vl _ _, Cancel) ->
        InitialState vl
    (CollectingSignatures vl (Payment vp _ _) _, Pay) ->
        let vl' = Value.minus vl vp in
        InitialState vl'
    _ -> error (traceH "invalid transition" ())

-- | @stepWithChecks params ptx state input@ computes the next state given
--   current state @state@ and the input. It checks whether the pending
--   transaction @ptx@ pays the expected amounts to script and public key
--   addresses. Fails with 'error' if an invalid transition is attempted.
stepWithChecks :: Params -> PendingTx -> State -> Input -> State
stepWithChecks p ptx s i =
    let newState = step s i in
    case (s, i) of
        (InitialState vl, ProposePayment pmt) ->
            if isValidProposal vl pmt &&
                valuePreserved vl ptx
            then newState
            else traceErrorH "ProposePayment invalid"
        (CollectingSignatures vl _ pks, AddSignature pk) ->
            if Validation.txSignedBy ptx pk &&
                isSignatory pk p &&
                not (containsPk pk pks) &&
                valuePreserved vl ptx
            then newState
            else traceErrorH "AddSignature invalid"
        (CollectingSignatures vl pmt _, Cancel) ->
            if proposalExpired ptx pmt &&
                valuePreserved vl ptx
            then InitialState vl
            else traceErrorH "Cancel invalid"
        (CollectingSignatures vl pmt@(Payment vp _ _) pks, Pay) ->
            let vl' = Value.minus vl vp in
            if not (proposalExpired ptx pmt) &&
                proposalAccepted p pks &&
                valuePreserved vl' ptx &&
                valuePaid pmt ptx
            then newState
            else traceErrorH "Pay invalid"
        _ -> traceErrorH "invalid transition"

mkValidator :: Params -> (State, Maybe Input) -> (State, Maybe Input) -> PendingTx -> Bool
mkValidator p ds vs ptx =
    let sm = StateMachine (stepWithChecks p ptx) in
    SM.mkValidator sm ds vs ptx

validator :: Params -> ValidatorScript
validator params = ValidatorScript $
    $$(Ledger.compileScript [|| mkValidator ||])
        `Ledger.applyScript`
            Ledger.lifted params

-- | Start watching the contract address
initialise :: WalletAPI m => Params -> m ()
initialise = WAPI.startWatching . Ledger.scriptAddress . validator

-- | Lock some funds in a multisig contract.
lock
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -- ^ Signatories and required signatures
    -> Value
    -- ^ The funds we want to lock
    -> m State
    -- ^ The initial state of the contract
lock prms vl = do
    let
        addr = Ledger.scriptAddress (validator prms)
        state = InitialState vl
        dataScript = DataScript (Ledger.lifted (SM.initialState @State @Input state))

    WAPI.payToScript_ WAPI.defaultSlotRange addr vl dataScript

    pure state

-- | Propose a payment from funds that are locked up in a state-machine based
--   multisig contract.
proposePayment
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> Payment
    -> m State
proposePayment prms st = mkStep prms st . ProposePayment

-- | Cancel a proposed payment
cancelPayment
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> m State
cancelPayment prms st = mkStep prms st Cancel

-- | Add a signature to a proposed payment
addSignature
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> m State
addSignature prms st = WAPI.ownPubKey >>= mkStep prms st . AddSignature

-- | Make a payment after enough signatures have been collected.
makePayment
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> m State
makePayment prms st = do
    -- we can't use 'mkStep' because the outputs of the transaction are
    -- different from the other transitions: We need two outputs, a public
    -- key output with the payment, and the script output with the remaining
    -- funds.
    (currentValue, valuePaid', recipient) <- case st of
        CollectingSignatures vl (Payment pd pk _) _ -> pure (vl, pd, pk)
        _ -> WAPI.throwOtherError "Cannot make payment because no payment has been proposed. Run the 'proposePayment' action first."

    let newState = step st Pay
        vl       = validator prms
        redeemer = RedeemerScript (Ledger.lifted (SM.transition newState Pay))
        dataScript = DataScript (Ledger.lifted (SM.transition newState Pay))

    inputs <- WAPI.spendScriptOutputs (Ledger.scriptAddress vl) vl redeemer
    let valueLeft = currentValue `Value.minus` valuePaid'
        scriptOut = Ledger.scriptTxOut valueLeft vl dataScript
        pkOut     = Ledger.pubKeyTxOut valuePaid' recipient
    _ <- WAPI.createTxAndSubmit WAPI.defaultSlotRange (Set.fromList $ fmap fst inputs) [scriptOut, pkOut]
    pure newState

-- | Advance a running multisig contract. This applies the transition function
--   'SM.transition' to the current contract state and uses the result to unlock
--   the funds currently in the contract, and lock them again with a data script
--   containing the new state.
--
mkStep
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -- ^ The parameters of the contract instance
    -> State
    -- ^ Current state of the instance
    -> Input
    -- ^ Input to be applied to the contract
    -> m State
    -- ^ New state after applying the input
mkStep prms st input = do
    let newState = step st input
        vl       = validator prms
        redeemer = RedeemerScript (Ledger.lifted (SM.transition newState input))
        dataScript = DataScript (Ledger.lifted (SM.transition newState input))

    inputs <- WAPI.spendScriptOutputs (Ledger.scriptAddress vl) vl redeemer
    let totalVal = foldMap snd inputs
        output = Ledger.scriptTxOut totalVal vl dataScript
    _ <- WAPI.createTxAndSubmit WAPI.defaultSlotRange (Set.fromList $ fmap fst inputs) [output]
    pure newState

{- Note [Current state of the contract]

The 'mkStep' function takes the current state of the contract and returns the
new state. Both values are placed on the chain, so technically we don't have to
pass them around like this, but we currently can't decode 'State' values from
PLC back to Haskell.

-}

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
    , mkValidator
    , scriptInstance
    , initialise
    , lock
    , proposePayment
    , cancelPayment
    , addSignature
    , makePayment
    ) where

import           Data.Functor                 (void)
import qualified Ledger.Interval              as Interval
import           Ledger.Validation            (PendingTx(..))
import qualified Ledger.Validation            as Validation
import qualified Ledger.Typed.Tx              as Typed
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import           Wallet
import qualified Wallet                       as WAPI
import qualified Wallet.Typed.API             as WAPITyped

import qualified Language.PlutusTx            as PlutusTx
import           Language.PlutusTx.Prelude     hiding (check)
import           Language.PlutusTx.StateMachine (StateMachine(..))
import qualified Language.PlutusTx.StateMachine as SM
import qualified Wallet.Typed.StateMachine as SM

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
proposalExpired (PendingTx _ _ _ _ _ rng _ _) (Payment _ _ ddl) = Interval.before ddl rng

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

{-# INLINABLE step #-}
-- | @step params state input@ computes the next state given current state
--   @state@ and the input.
--   'step' does not perform any checks of the preconditions. This is done in
--   'check' below.
step :: State -> Input -> Maybe State
step s i = case (s, i) of
    (InitialState vl, ProposePayment pmt) ->
        Just $ CollectingSignatures vl pmt []
    (CollectingSignatures vl pmt pks, AddSignature pk) ->
        Just $ CollectingSignatures vl pmt (pk:pks)
    (CollectingSignatures vl _ _, Cancel) ->
        Just $ InitialState vl
    (CollectingSignatures vl (Payment vp _ _) _, Pay) ->
        let vl' = vl - vp in
        Just $ InitialState vl'
    _ -> Nothing

{-# INLINABLE check #-}
-- | @check params ptx state input@ checks whether the pending
--   transaction @ptx@ pays the expected amounts to script and public key
--   addresses.
check :: Params -> State -> Input -> PendingTx -> Bool
check p s i ptx = case (s, i) of
    (InitialState vl, ProposePayment pmt) ->
        isValidProposal vl pmt && valuePreserved vl ptx
    (CollectingSignatures vl _ pks, AddSignature pk) ->
        Validation.txSignedBy ptx pk &&
            isSignatory pk p &&
            not (containsPk pk pks) &&
            valuePreserved vl ptx
    (CollectingSignatures vl pmt _, Cancel) ->
        proposalExpired ptx pmt && valuePreserved vl ptx
    (CollectingSignatures vl pmt@(Payment vp _ _) pks, Pay) ->
        let vl' = vl - vp in
        not (proposalExpired ptx pmt) &&
            proposalAccepted p pks &&
            valuePreserved vl' ptx &&
            valuePaid pmt ptx
    _ -> False

{-# INLINABLE mkValidator #-}
mkValidator :: Params -> SM.StateMachineValidator State Input
mkValidator p = SM.mkValidator $ StateMachine step (check p)

validatorCode :: Params -> PlutusTx.CompiledCode (Typed.ValidatorType MultiSigSym)
validatorCode params = $$(PlutusTx.compile [|| mkValidator ||]) `PlutusTx.applyCode` PlutusTx.unsafeLiftCode params

type MultiSigSym = StateMachine State Input
scriptInstance :: Params -> Typed.ScriptInstance MultiSigSym
scriptInstance params = Typed.Validator $ validatorCode params

machineInstance :: Params -> SM.StateMachineInstance State Input
machineInstance params =
    SM.StateMachineInstance
    (StateMachine step (check params))
    (scriptInstance params)
    redeemerCode

-- | Start watching the contract address
initialise :: WalletAPI m => Params -> m ()
initialise = WAPI.startWatching . Typed.scriptAddress . scriptInstance

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
    (tx, state) <- SM.initialise (machineInstance prms) (InitialState vl) vl

    void $ WAPITyped.signTxAndSubmit tx

    pure state

-- | Propose a payment from funds that are locked up in a state-machine based
--   multisig contract.
proposePayment
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> Payment
    -> m State
proposePayment prms st = runStep prms st . ProposePayment

-- | Cancel a proposed payment
cancelPayment
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> m State
cancelPayment prms st = runStep prms st Cancel

-- | Add a signature to a proposed payment
addSignature
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> m State
addSignature prms st = WAPI.ownPubKey >>= runStep prms st . AddSignature

-- | Make a payment after enough signatures have been collected.
makePayment
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> m State
makePayment prms currentState = do
    -- we can't use 'runStep' because the outputs of the transaction are
    -- different from the other transitions: We need two outputs, a public
    -- key output with the payment, and the script output with the remaining
    -- funds.
    (currentValue, valuePaid', recipient) <- case currentState of
        CollectingSignatures vl (Payment pd pk _) _ -> pure (vl, pd, pk)
        _ -> WAPI.throwOtherError "Cannot make payment because no payment has been proposed. Run the 'proposePayment' action first."
    let valueLeft = currentValue - valuePaid'

    (scriptTx, newState) <- SM.mkStep (machineInstance prms) currentState Pay (const valueLeft)

    -- Need to match to get the existential type out
    case scriptTx of
        (Typed.TypedTxSomeIns tx) -> do
            let pkOut = Typed.makePubKeyTxOut valuePaid' recipient
                withPubKeyOut = tx { Typed.tyTxPubKeyTxOuts = [pkOut] }
            void $ WAPITyped.signTxAndSubmit withPubKeyOut

    pure newState

redeemerCode :: PlutusTx.CompiledCode (Input -> Typed.RedeemerFunctionType '[MultiSigSym] MultiSigSym)
redeemerCode = $$(PlutusTx.compile [|| SM.mkRedeemer @State @Input ||])

-- | Advance a running multisig contract. This applies the transition function
--   'SM.transition' to the current contract state and uses the result to unlock
--   the funds currently in the contract, and lock them again with a data script
--   containing the new state.
--
runStep
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -- ^ The parameters of the contract instance
    -> State
    -- ^ Current state of the instance
    -> Input
    -- ^ Input to be applied to the contract
    -> m State
    -- ^ New state after applying the input
runStep prms currentState input = do
    (scriptTx, newState) <- SM.mkStep (machineInstance prms) currentState input id

    -- Need to match to get the existential type out
    case scriptTx of
        (Typed.TypedTxSomeIns tx) -> void $ WAPITyped.signTxAndSubmit tx

    pure newState

{- Note [Current state of the contract]

The 'mkStep' function takes the current state of the contract and returns the
new state. Both values are placed on the chain, so technically we don't have to
pass them around like this, but we currently can't decode 'State' values from
PLC back to Haskell.

-}

{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
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
import           Ledger.Validation            (PendingTx)
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import           Wallet
import qualified Wallet                       as WAPI

import           Language.PlutusTx.StateMachine
import           Language.PlutusTx.Coordination.Contracts.MultiSig.Stage0 as MultiSig
import qualified Language.PlutusTx.StateMachine as SM

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

validator :: Params -> ValidatorScript
validator params = ValidatorScript val where
    val = Ledger.applyScript script (Ledger.lifted params)

    script = ($$(Ledger.compileScript [||

        \(p :: Params) (ds :: (State, Maybe Input)) (vs :: (State, Maybe Input)) (ptx :: PendingTx) ->
            let
                trans = $$stepWithChecks p ptx
                sm = StateMachine trans $$stateEq
            in $$(mkValidator) sm ds vs ptx

        ||]))

-- | Start watching the contract address
initialise :: WalletAPI m => Params -> m ()
initialise = WAPI.startWatching . Ledger.scriptAddress . validator

-- | Lock some funds in a multisig contract.
lock
    :: (WalletAPI m, WalletDiagnostics m)
    => MultiSig.Params
    -- ^ Signatories and required signatures
    -> Value
    -- ^ The funds we want to lock
    -> m MultiSig.State
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
    => MultiSig.Params
    -> MultiSig.State
    -> MultiSig.Payment
    -> m MultiSig.State
proposePayment prms st = mkStep prms st . ProposePayment

-- | Cancel a proposed payment
cancelPayment
    :: (WalletAPI m, WalletDiagnostics m)
    => MultiSig.Params
    -> MultiSig.State
    -> m MultiSig.State
cancelPayment prms st = mkStep prms st Cancel

-- | Add a signature to a proposed payment
addSignature
    :: (WalletAPI m, WalletDiagnostics m)
    => MultiSig.Params
    -> MultiSig.State
    -> m MultiSig.State
addSignature prms st = WAPI.ownPubKey >>= mkStep prms st . AddSignature

-- | Make a payment after enough signatures have been collected.
makePayment
    :: (WalletAPI m, WalletDiagnostics m)
    => MultiSig.Params
    -> MultiSig.State
    -> m MultiSig.State
makePayment prms st = do
    -- we can't use 'mkStep' because the outputs of the transaction are
    -- different from the other transitions: We need two outputs, a public
    -- key output with the payment, and the script output with the remaining
    -- funds.
    (currentValue, valuePaid, recipient) <- case st of
        CollectingSignatures vl (Payment pd pk _) _ -> pure (vl, pd, pk)
        _ -> WAPI.throwOtherError "Cannot make payment because no payment has been proposed. Run the 'proposePayment' action first."

    let newState = $$step st Pay
        vl       = validator prms
        redeemer = RedeemerScript (Ledger.lifted (SM.transition newState Pay))
        dataScript = DataScript (Ledger.lifted (SM.transition newState Pay))

    inputs <- WAPI.spendScriptOutputs (Ledger.scriptAddress vl) vl redeemer
    let valueLeft = currentValue `Value.minus` valuePaid
        scriptOut = Ledger.scriptTxOut valueLeft vl dataScript
        pkOut     = Ledger.pubKeyTxOut valuePaid recipient
    _ <- WAPI.createTxAndSubmit WAPI.defaultSlotRange (Set.fromList $ fmap fst inputs) [scriptOut, pkOut]
    pure newState

-- | Advance a running multisig contract. This applies the transition function
--   'SM.transition' to the current contract state and uses the result to unlock
--   the funds currently in the contract, and lock them again with a data script
--   containing the new state.
--
mkStep
    :: (WalletAPI m, WalletDiagnostics m)
    => MultiSig.Params
    -- ^ The parameters of the contract instance
    -> MultiSig.State
    -- ^ Current state of the instance
    -> MultiSig.Input
    -- ^ Input to be applied to the contract
    -> m MultiSig.State
    -- ^ New state after applying the input
mkStep prms st input = do
    let newState = $$step st input
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

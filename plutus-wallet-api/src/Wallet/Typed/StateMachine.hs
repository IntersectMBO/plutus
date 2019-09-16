{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Wallet.Typed.StateMachine where

import           Control.Monad
import qualified Data.Text                      as T

import qualified Language.PlutusTx              as PlutusTx
import qualified Language.PlutusTx.StateMachine as SM
import qualified Ledger.Typed.Tx                as Typed
import           Ledger.Value
import qualified Wallet.API                     as WAPI
import qualified Wallet.Typed.API               as WAPITyped

mkInitialise
    :: forall s i m
    . (WAPI.WalletAPI m, WAPI.WalletDiagnostics m, PlutusTx.Lift s)
    => SM.StateMachineInstance s i
    -- ^ Signatories and required signatures
    -> s
    -- ^ Initial state.
    -> Value
    -- ^ The funds we want to lock.
    -> m (Typed.TypedTx '[] '[SM.StateMachine s i], s)
    -- ^ The initalizing transaction and the initial state of the contract.
mkInitialise (SM.StateMachineInstance _ si _ _) state vl = do
    let dataScript = PlutusTx.unsafeLiftCode state

    tx <- WAPITyped.makeScriptPayment si WAPI.defaultSlotRange vl dataScript

    pure (tx, state)

-- | Advance a running state machine contract. This applies the transition function
--   to the current contract state and uses the result to unlock
--   the funds currently in the contract, and lock them again with a data script
--   containing the new state.
--
mkStep
    :: forall s i m
    . (WAPI.WalletAPI m, WAPI.WalletDiagnostics m, PlutusTx.Lift s, PlutusTx.Typeable s, PlutusTx.Lift i)
    => SM.StateMachineInstance s i
    -- ^ The parameters of the contract instance
    -> s
    -- ^ Current state of the instance
    -> i
    -- ^ Input to be applied to the contract
    -> (Value -> Value)
    -- ^ Function determining how much of the total incoming value to the outgoing script output.
    -> m (Typed.TypedTxSomeIns '[SM.StateMachine s i], s)
    -- ^ The advancing transaction, which consumes all the outputs at the script address, and the new state after applying the input
mkStep (SM.StateMachineInstance (SM.StateMachine step _ _) si stepRedeemer _) currentState input valueAllocator = do
    newState <- case step currentState input of
        Just s  -> pure s
        Nothing -> WAPI.throwOtherError "Invalid transition"
    let redeemer :: PlutusTx.CompiledCode (Typed.RedeemerFunctionType '[SM.StateMachine s i] (SM.StateMachine s i))
        redeemer = stepRedeemer `PlutusTx.applyCode` PlutusTx.unsafeLiftCode input
        dataScript :: PlutusTx.CompiledCode s
        dataScript = PlutusTx.unsafeLiftCode newState

    -- TODO: This needs to check that all the inputs have exactly the state we specify as the argument here,
    -- otherwise you can poison the contract by adding a state machine output that's not in the same state.
    -- We'd try and advance both to the new state in one transaction, and validation of the second one
    -- would fail.
    typedIns <- WAPITyped.spendScriptOutputs si redeemer
    let totalVal = foldMap snd typedIns
        output = Typed.makeTypedScriptTxOut si dataScript (valueAllocator totalVal)
        txWithOuts = Typed.addTypedTxOut output Typed.baseTx
        fullTx :: Typed.TypedTxSomeIns '[SM.StateMachine s i]
        fullTx = Typed.addManyTypedTxIns (fmap fst typedIns) txWithOuts

    pure (fullTx, newState)

-- | Halt a running state machine contract. This applies the transition function
--   to the current contract state and checks that the resulting state is final.
--   The transaction will have no ongoing script output.
--
mkHalt
    :: forall s i m
    . (Show s, WAPI.WalletAPI m, WAPI.WalletDiagnostics m, PlutusTx.Typeable s, PlutusTx.Lift i)
    => SM.StateMachineInstance s i
    -- ^ The parameters of the contract instance
    -> s
    -- ^ Current state of the instance
    -> i
    -- ^ Input to be applied to the contract
    -> m (Typed.TypedTxSomeIns '[], s)
    -- ^ The advancing transaction, which consumes all the outputs at the script address.
mkHalt (SM.StateMachineInstance (SM.StateMachine step _ final) si _ haltRedeemer) currentState input = do
    newState <- case step currentState input of
        Just s  -> pure s
        Nothing -> WAPI.throwOtherError "Invalid transition"
    unless (final newState) $ WAPI.throwOtherError $ "Cannot halt when transitioning to a non-final state: " <> (T.pack $ show newState)
    let redeemer :: PlutusTx.CompiledCode (Typed.RedeemerFunctionType '[] (SM.StateMachine s i))
        redeemer = haltRedeemer `PlutusTx.applyCode` PlutusTx.unsafeLiftCode input

    -- TODO: This needs to check that all the inputs have exactly the state we specify as the argument here,
    -- otherwise you can poison the contract by adding a state machine output that's not in the same state.
    -- We'd try and advance both to the new state in one transaction, and validation of the second one
    -- would fail.
    typedIns <- WAPITyped.spendScriptOutputs si redeemer
    let fullTx :: Typed.TypedTxSomeIns '[]
        fullTx = Typed.addManyTypedTxIns (fmap fst typedIns) Typed.baseTx

    pure (fullTx, newState)

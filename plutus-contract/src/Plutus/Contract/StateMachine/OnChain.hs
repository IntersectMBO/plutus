{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | On-chain code fragments for creating a state machine. First
--   define a @StateMachine s i@ with input type @i@ and state type @s@. Then
--   use 'mkValidator' in on-chain code to check the required hashes and
--   validate the transition, and 'mkRedeemer' to make redeemer scripts.
module Plutus.Contract.StateMachine.OnChain(
      StateMachine(..)
    , StateMachineInstance (..)
    , State(..)
    , mkStateMachine
    , mkStateMachineTT
    , machineAddress
    , mkValidator
    , threadTokenValue
    ) where

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Void                        (Void)
import           GHC.Generics                     (Generic)
import           Ledger                           (Address, TxOutRef, ValidatorHash (..))
import           Ledger.Constraints
import           Ledger.Constraints.TxConstraints (OutputConstraint (..))
import           Ledger.Contexts                  (ScriptContext (..), TxInInfo (..), findOwnInput, ownHash)
import           Ledger.Tx                        (TxOut (..))
import           Ledger.Typed.Scripts
import           Ledger.Value                     (CurrencySymbol, TokenName (..), Value (..), isZero)
import qualified Ledger.Value                     as Value
import qualified PlutusTx                         as PlutusTx
import qualified PlutusTx.AssocMap                as Map
import           PlutusTx.Prelude                 hiding (check)
import qualified Prelude                          as Haskell

data State s = State { stateData :: s, stateValue :: Value }
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Specification of a state machine, consisting of a transition function that determines the
-- next state from the current state and an input, and a checking function that checks the validity
-- of the transition in the context of the current transaction.
data StateMachine s i = StateMachine {
      -- | The transition function of the state machine. 'Nothing' indicates an invalid transition from the current state.
      smTransition  :: State s -> i -> Maybe (TxConstraints Void Void, State s),

      -- | Check whether a state is the final state
      smFinal       :: s -> Bool,

      -- | The condition checking function. Can be used to perform
      --   checks on the pending transaction that aren't covered by the
      --   constraints. 'smCheck' is always run in addition to checking the
      --   constraints, so the default implementation always returns true.
      smCheck       :: s -> i -> ScriptContext -> Bool,

      -- | The 'AssetClass' of the thread token that identifies the contract
      --   instance.
      smThreadToken :: Maybe CurrencySymbol,

      smTxOutRef    :: Maybe TxOutRef
    }

{-# INLINABLE threadTokenValueInner #-}
-- | The 'Value' containing exactly the thread token, if one has been specified.
threadTokenValueInner :: Maybe CurrencySymbol -> ValidatorHash -> Value
threadTokenValueInner currency (ValidatorHash vHash) = maybe mempty (\c -> Value.singleton c (TokenName vHash) 1) currency

{-# INLINABLE threadTokenValue #-}
threadTokenValue :: StateMachineInstance s i -> Value
threadTokenValue StateMachineInstance{stateMachine,typedValidator} =
    threadTokenValueInner (smThreadToken stateMachine) (validatorHash typedValidator)

{-# INLINABLE checkThreadToken #-}
checkThreadToken :: Maybe CurrencySymbol -> ValidatorHash -> Value -> Bool
checkThreadToken Nothing _ _ = True
checkThreadToken (Just currency) (ValidatorHash vHash) (Value vl) =
    case Map.toList <$> Map.lookup currency vl of
        Just [(TokenName tHash, _)] -> tHash == vHash
        _                           -> False

-- | A state machine that does not perform any additional checks on the
--   'ScriptContext' (beyond enforcing the constraints)
mkStateMachine
    :: Maybe TxOutRef
    -> (State s -> i -> Maybe (TxConstraints Void Void, State s))
    -> (s -> Bool)
    -> StateMachine s i
mkStateMachine Nothing smTransition smFinal =
    StateMachine
        { smTransition
        , smFinal
        , smCheck = \_ _ _ -> True
        , smThreadToken = Nothing
        , smTxOutRef = Nothing
        }
mkStateMachine (Just _) _ _ = error ()

mkStateMachineTT
    :: TxOutRef
    -> CurrencySymbol
    -> (State s -> i -> Maybe (TxConstraints Void Void, State s))
    -> (s -> Bool)
    -> StateMachine s i
mkStateMachineTT outRef cur smTransition smFinal =
    StateMachine
        { smTransition
        , smFinal
        , smCheck = \_ _ _ -> True
        , smThreadToken = Just cur
        , smTxOutRef = Just outRef
        }

instance ValidatorTypes (StateMachine s i) where
    type instance RedeemerType (StateMachine s i) = i
    type instance DatumType (StateMachine s i) = s

data StateMachineInstance s i = StateMachineInstance {
    -- | The state machine specification.
    stateMachine   :: StateMachine s i,
    -- | The validator code for this state machine.
    typedValidator :: TypedValidator (StateMachine s i)
    }

machineAddress :: StateMachineInstance s i -> Address
machineAddress = validatorAddress . typedValidator

{-# INLINABLE mkValidator #-}
-- | Turn a state machine into a validator script.
mkValidator :: forall s i. (PlutusTx.IsData s) => StateMachine s i -> ValidatorType (StateMachine s i)
mkValidator (StateMachine step isFinal check currency _) currentState input ptx =
    let vl = maybe (error ()) (txOutValue . txInInfoResolved) (findOwnInput ptx)
        checkOk =
            traceIfFalse "State transition invalid - checks failed" (check currentState input ptx)
            && traceIfFalse "Thread token hash mismatch" (checkThreadToken currency (ownHash ptx) vl)
        oldState = State{stateData=currentState, stateValue=vl}
        stateAndOutputsOk = case step oldState input of
            Just (newConstraints, State{stateData=newData, stateValue=newValue})
                | isFinal newData ->
                    traceIfFalse "Non-zero value allocated in final state" (isZero newValue)
                    && traceIfFalse "State transition invalid - constraints not satisfied by ScriptContext" (checkScriptContext newConstraints ptx)
                | otherwise ->
                    let txc =
                            newConstraints
                                { txOwnOutputs=
                                    [ OutputConstraint
                                        { ocDatum = newData
                                        , ocValue = newValue <> threadTokenValueInner currency (ownHash ptx)
                                        }
                                    ]
                                }
                    in traceIfFalse "State transition invalid - constraints not satisfied by ScriptContext" (checkScriptContext @_ @s txc ptx)
            Nothing -> trace "State transition invalid - input is not a valid transition at the current state" False
    in checkOk && stateAndOutputsOk

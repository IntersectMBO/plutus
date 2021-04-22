{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}
-- | A state machine with two states and two roles that take turns.
module Plutus.Contracts.PingPong(
    PingPongState(..),
    Input(..),
    PingPongError(..),
    PingPongSchema,
    runPing,
    runPong,
    initialise,
    runStop,
    runWaitForUpdate
    ) where

import           Control.Lens
import           Control.Monad                (void)
import           Data.Aeson                   (FromJSON, ToJSON)
import           GHC.Generics                 (Generic)
import qualified Ledger.Ada                   as Ada
import           Ledger.Constraints           (TxConstraints)
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Typed.Tx              (tyTxOutData)
import qualified PlutusTx                     as PlutusTx
import           PlutusTx.Prelude             hiding (Applicative (..), check)

import           Plutus.Contract.StateMachine (AsSMContractError (..), OnChainState, State (..), Void)
import qualified Plutus.Contract.StateMachine as SM

import           Plutus.Contract

data PingPongState = Pinged | Ponged | Stopped
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Eq PingPongState where
    Pinged == Pinged = True
    Ponged == Ponged = True
    _ == _           = False

data Input = Ping | Pong | Stop
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

type PingPongSchema =
    BlockchainActions
        .\/ Endpoint "initialise" ()
        .\/ Endpoint "ping" ()
        .\/ Endpoint "pong" ()
        .\/ Endpoint "stop" () -- Transition the state machine instance to the final state
        .\/ Endpoint "wait" () -- Wait for a change to the on-chain state of the machine

data PingPongError =
    PingPongContractError ContractError
    | PingPongSMError SM.SMContractError
    | StoppedUnexpectedly
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''PingPongError

instance AsSMContractError PingPongError where
    _SMContractError = _PingPongSMError

instance AsContractError PingPongError where
    _ContractError = _PingPongContractError

{-# INLINABLE transition #-}
transition :: State PingPongState -> Input -> Maybe (TxConstraints Void Void, State PingPongState)
transition State{stateData=oldData,stateValue} input = case (oldData, input) of
    (_,      Stop) -> Just (mempty, State{stateData=Stopped, stateValue=mempty})
    (Pinged, Pong) -> Just (mempty, State{stateData=Ponged, stateValue})
    (Ponged, Ping) -> Just (mempty, State{stateData=Pinged, stateValue})
    _              -> Nothing

{-# INLINABLE machine #-}
machine :: SM.StateMachine PingPongState Input
machine = SM.mkStateMachine Nothing transition isFinal where
    isFinal Stopped = True
    isFinal _       = False

{-# INLINABLE mkValidator #-}
mkValidator :: Scripts.ValidatorType (SM.StateMachine PingPongState Input)
mkValidator = SM.mkValidator machine

scriptInstance :: Scripts.ScriptInstance (SM.StateMachine PingPongState Input)
scriptInstance = Scripts.validator @(SM.StateMachine PingPongState Input)
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @PingPongState @Input

machineInstance :: SM.StateMachineInstance PingPongState Input
machineInstance = SM.StateMachineInstance machine scriptInstance

client :: SM.StateMachineClient PingPongState Input
client = SM.mkStateMachineClient machineInstance

initialise :: Contract () PingPongSchema PingPongError PingPongState
initialise = endpoint @"initialise" >> SM.runInitialise client Pinged (Ada.lovelaceValueOf 1)

run ::
    PingPongState
    -> Contract () PingPongSchema PingPongError ()
    -> Contract () PingPongSchema PingPongError ()
run expectedState action = do
    let extractState = tyTxOutData . fst
        go Nothing = throwError StoppedUnexpectedly
        go (Just currentState)
            | extractState currentState == expectedState = action
            | otherwise = SM.waitForUpdate client >>= go
    maybeState <- SM.getOnChainState client
    let datum = fmap fst maybeState
    go datum

runPing :: Contract () PingPongSchema PingPongError ()
runPing = run Ponged (endpoint @"ping" >> void (SM.runStep client Ping))

runPong :: Contract () PingPongSchema PingPongError ()
runPong = run Pinged (endpoint @"pong" >> void (SM.runStep client Pong))

runStop :: Contract () PingPongSchema PingPongError ()
runStop = endpoint @"stop" >> void (SM.runStep client Stop)

runWaitForUpdate :: Contract () PingPongSchema PingPongError (Maybe (OnChainState PingPongState Input))
runWaitForUpdate = SM.waitForUpdate client

PlutusTx.unstableMakeIsData ''PingPongState
PlutusTx.makeLift ''PingPongState
PlutusTx.unstableMakeIsData ''Input
PlutusTx.makeLift ''Input

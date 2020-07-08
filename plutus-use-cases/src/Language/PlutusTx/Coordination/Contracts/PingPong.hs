{-# LANGUAGE DataKinds             #-}
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
{-# OPTIONS -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
-- | A state machine with two states and two roles that take turns.
module Language.PlutusTx.Coordination.Contracts.PingPong(
    PingPongState(..),
    Input(..),
    PingPongError(..),
    PingPongSchema,
    runPing,
    runPong,
    initialise
    ) where

import           Control.Lens
import           Control.Monad                         (void)
import qualified Language.PlutusTx                     as PlutusTx
import           Language.PlutusTx.Prelude             hiding (Applicative (..), check)
import qualified Ledger.Ada                            as Ada
import           Ledger.Constraints                    (TxConstraints)
import qualified Ledger.Typed.Scripts                  as Scripts
import           Ledger.Typed.Tx                       (tyTxOutData)

import           Language.Plutus.Contract.StateMachine (AsSMContractError (..), State (..), Void)
import qualified Language.Plutus.Contract.StateMachine as SM

import           Language.Plutus.Contract

data PingPongState = Pinged | Ponged
    deriving stock Show

instance Eq PingPongState where
    Pinged == Pinged = True
    Ponged == Ponged = True
    _ == _ = False

data Input = Ping | Pong
    deriving stock Show

type PingPongSchema =
    BlockchainActions
        .\/ Endpoint "initialise" ()
        .\/ Endpoint "ping" ()
        .\/ Endpoint "pong" ()

data PingPongError =
    PingPongContractError ContractError
    | PingPongSMError (SM.SMContractError PingPongState Input)
    deriving stock (Show)

makeClassyPrisms ''PingPongError

instance AsSMContractError PingPongError PingPongState Input where
    _SMContractError = _PingPongSMError

instance AsContractError PingPongError where
    _ContractError = _PingPongContractError

{-# INLINABLE transition #-}
transition :: State PingPongState -> Input -> Maybe (TxConstraints Void Void, State PingPongState)
transition State{stateData=oldData,stateValue} input = case (oldData, input) of
    (Pinged, Pong) -> Just (mempty, State{stateData=Ponged, stateValue})
    (Ponged, Ping) -> Just (mempty, State{stateData=Pinged, stateValue})
    _              -> Nothing

{-# INLINABLE machine #-}
machine :: SM.StateMachine PingPongState Input
machine = SM.mkStateMachine transition isFinal where
    isFinal _ = False

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

initialise :: Contract PingPongSchema PingPongError PingPongState
initialise = endpoint @"initialise" >> SM.runInitialise client Pinged (Ada.lovelaceValueOf 1)

run ::
    PingPongState
    -> Contract PingPongSchema PingPongError ()
    -> Contract PingPongSchema PingPongError ()
run expectedState action = do
    (st, _) <- SM.getOnChainState client
    let extractState = tyTxOutData . fst
        go currentState
            | extractState currentState == expectedState = action
            | otherwise = SM.waitForUpdate client >>= go
    go st

runPing :: Contract PingPongSchema PingPongError ()
runPing = run Ponged (endpoint @"ping" >> void (SM.runStep client Ping))

runPong :: Contract PingPongSchema PingPongError ()
runPong = run Pinged (endpoint @"pong" >> void (SM.runStep client Pong))

PlutusTx.makeIsData ''PingPongState
PlutusTx.makeLift ''PingPongState
PlutusTx.makeIsData ''Input
PlutusTx.makeLift ''Input


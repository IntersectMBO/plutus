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
{-# OPTIONS -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
-- | A guessing game that
--
--   * Uses a state machine to keep track of the current secret word
--   * Uses a token to keep track of who is allowed to make a guess
--

module Language.PlutusTx.Coordination.Contracts.GameStateMachine(
    contract
    , scriptInstance
    , GameToken
    , mkValidator
    , monetaryPolicy
    , LockArgs(..)
    , GuessArgs(..)
    , GameStateMachineSchema
    , token
    ) where

import           Control.Monad                         (void)
import           Data.Aeson                            (FromJSON, ToJSON)
import           GHC.Generics                          (Generic)
import qualified Language.PlutusTx                     as PlutusTx
import           Language.PlutusTx.Prelude             hiding (Applicative (..), check)
import           Ledger                                hiding (to)
import           Ledger.Constraints                    (TxConstraints)
import qualified Ledger.Constraints                    as Constraints
import qualified Ledger.Typed.Scripts                  as Scripts
import qualified Ledger.Value                          as V

import qualified Data.ByteString.Char8                 as C

import           Language.Plutus.Contract.StateMachine (State (..), Void)
import qualified Language.Plutus.Contract.StateMachine as SM

import           Language.Plutus.Contract

newtype HashedString = HashedString ByteString
    deriving newtype (PlutusTx.IsData, Eq)
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString
    deriving newtype (PlutusTx.IsData, Eq)
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeLift ''ClearString

-- | Arguments for the @"lock"@ endpoint
data LockArgs =
    LockArgs
        { lockArgsSecret :: String
        -- ^ The secret
        , lockArgsValue  :: Value
        -- ^ Value that is locked by the contract initially
        } deriving stock (Show, Generic)
          deriving anyclass (ToJSON, FromJSON)

-- | Arguments for the @"guess"@ endpoint
data GuessArgs =
    GuessArgs
        { guessArgsOldSecret     :: String
        -- ^ The guess
        , guessArgsNewSecret     :: String
        -- ^ The new secret
        , guessArgsValueTakenOut :: Value
        -- ^ How much to extract from the contract
        } deriving stock (Show, Generic)
          deriving anyclass (ToJSON, FromJSON)

-- | The schema of the contract. It consists of the usual
--   'BlockchainActions' plus the two endpoints @"lock"@
--   and @"guess"@ with their respective argument types.
type GameStateMachineSchema =
    BlockchainActions
        .\/ Endpoint "lock" LockArgs
        .\/ Endpoint "guess" GuessArgs

data GameError =
    GameContractError ContractError
    | GameSMError SM.SMContractError
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Top-level contract, exposing both endpoints.
contract :: Contract GameStateMachineSchema GameError ()
contract = (lock `select` guess) >> contract

-- | The token that represents the right to make a guess
newtype GameToken = GameToken { unGameToken :: Value }
    deriving newtype (Eq, Show)

token :: MonetaryPolicyHash -> TokenName -> Value
token mps tn = V.singleton (V.mpsSymbol mps) tn 1

-- | State of the guessing game
data GameState =
    Initialised MonetaryPolicyHash TokenName HashedString
    -- ^ Initial state. In this state only the 'ForgeTokens' action is allowed.
    | Locked MonetaryPolicyHash TokenName HashedString
    -- ^ Funds have been locked. In this state only the 'Guess' action is
    --   allowed.
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Eq GameState where
    {-# INLINABLE (==) #-}
    (Initialised sym tn s) == (Initialised sym' tn' s') = sym == sym' && s == s' && tn == tn'
    (Locked sym tn s) == (Locked sym' tn' s')           = sym == sym' && s == s' && tn == tn'
    _ == _                                              = traceIfFalse "states not equal" False

-- | Check whether a 'ClearString' is the preimage of a
--   'HashedString'
checkGuess :: HashedString -> ClearString -> Bool
checkGuess (HashedString actual) (ClearString gss) = actual == (sha2_256 gss)

-- | Inputs (actions)
data GameInput =
      ForgeToken
    -- ^ Forge the "guess" token
    | Guess ClearString HashedString Value
    -- ^ Make a guess, extract the funds, and lock the remaining funds using a
    --   new secret word.
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

{-# INLINABLE transition #-}
transition :: State GameState -> GameInput -> Maybe (TxConstraints Void Void, State GameState)
transition State{stateData=oldData, stateValue=oldValue} input = case (oldData, input) of
    (Initialised mph tn s, ForgeToken) ->
        let constraints = Constraints.mustForgeCurrency mph tn 1 in
        Just ( constraints
             , State
                { stateData = Locked mph tn s
                , stateValue = oldValue
                }
             )
    (Locked mph tn currentSecret, Guess theGuess nextSecret takenOut)
        | checkGuess currentSecret theGuess ->
        let constraints = Constraints.mustSpendValue (token mph tn) <> Constraints.mustForgeCurrency mph tn 0 in
        Just ( constraints
             , State
                { stateData = Locked mph tn nextSecret
                , stateValue = oldValue - takenOut
                }
             )
    _ -> Nothing

{-# INLINABLE machine #-}
machine :: SM.StateMachine GameState GameInput
machine = SM.mkStateMachine transition isFinal where
    isFinal _ = False

{-# INLINABLE mkValidator #-}
mkValidator :: Scripts.ValidatorType (SM.StateMachine GameState GameInput)
mkValidator = SM.mkValidator machine

scriptInstance :: Scripts.ScriptInstance (SM.StateMachine GameState GameInput)
scriptInstance = Scripts.validator @(SM.StateMachine GameState GameInput)
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @GameState @GameInput

monetaryPolicy :: Scripts.MonetaryPolicy
monetaryPolicy = Scripts.monetaryPolicy scriptInstance

-- | The 'SM.StateMachineInstance' of the game state machine contract. It uses
--   the functions in 'Language.PlutusTx.StateMachine' to generate a validator
--   script based on the functions 'step' and 'check' we defined above.
machineInstance :: SM.StateMachineInstance GameState GameInput
machineInstance = SM.StateMachineInstance machine scriptInstance

client :: SM.StateMachineClient GameState GameInput
client = SM.mkStateMachineClient machineInstance

-- | The @"guess"@ endpoint.
guess :: Contract GameStateMachineSchema GameError ()
guess = do
    GuessArgs{guessArgsOldSecret,guessArgsNewSecret, guessArgsValueTakenOut} <- mapError GameContractError $ endpoint @"guess"

    let guessedSecret = ClearString (C.pack guessArgsOldSecret)
        newSecret     = HashedString (sha2_256 (C.pack guessArgsNewSecret))

    void
        $ mapError GameSMError
        $ SM.runStep client
            (Guess guessedSecret newSecret guessArgsValueTakenOut)

lock :: Contract GameStateMachineSchema GameError ()
lock = do
    LockArgs{lockArgsSecret, lockArgsValue} <- mapError GameContractError $ endpoint @"lock"
    let secret = HashedString (sha2_256 (C.pack lockArgsSecret))
        sym = Scripts.monetaryPolicyHash scriptInstance
    _ <- mapError GameSMError $ SM.runInitialise client (Initialised sym "guess" secret) lockArgsValue
    void $ mapError GameSMError $ SM.runStep client ForgeToken

PlutusTx.makeIsData ''GameState
PlutusTx.makeLift ''GameState
PlutusTx.makeIsData ''GameInput
PlutusTx.makeLift ''GameInput
PlutusTx.makeLift ''GameToken
PlutusTx.makeIsData ''GameToken

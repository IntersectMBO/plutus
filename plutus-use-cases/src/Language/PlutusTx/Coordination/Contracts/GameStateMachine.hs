{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE NoImplicitPrelude #-}
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
    , gameTokenVal
    , mkValidator
    , LockArgs(..)
    , GuessArgs(..)
    , GameStateMachineSchema
    ) where

import Control.Lens (makeClassyPrisms)
import           Control.Monad                (void)
import qualified Language.PlutusTx            as PlutusTx
import           Language.PlutusTx.Prelude    hiding (check, Applicative (..), (<>))
import           Ledger                       hiding (to)
import           Ledger.Value                 (TokenName)
import qualified Ledger.Value                 as V
import qualified Ledger.Validation            as Validation
import qualified Ledger.Typed.Scripts         as Scripts

import qualified Data.ByteString.Lazy.Char8   as C

import           Language.Plutus.Contract.StateMachine (ValueAllocation(..), AsSMContractError)
import qualified Language.Plutus.Contract.StateMachine as SM

import           Language.Plutus.Contract
import qualified Language.Plutus.Contract.Tx as Tx
import qualified Prelude as Haskell

newtype HashedString = HashedString ByteString
    deriving newtype PlutusTx.IsData
    deriving stock Show

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString
    deriving newtype PlutusTx.IsData
    deriving stock Show

PlutusTx.makeLift ''ClearString

-- | Arguments for the @"lock"@ endpoint
data LockArgs =
    LockArgs
        { lockArgsSecret :: String
        -- ^ The secret
        , lockArgsValue  :: Value
        -- ^ Value that is locked by the contract initially
        } deriving Show

-- | Arguments for the @"guess"@ endpoint
data GuessArgs =
    GuessArgs
        { guessArgsOldSecret :: String
        -- ^ The guess
        , guessArgsNewSecret :: String
        -- ^ The new secret
        , guessArgsValueTakenOut :: Value
        -- ^ How much to extract from the contract
        } deriving Show

-- | The schema of the contract. It consists of the usual
--   'BlockchainActions' plus the two endpoints @"lock"@
--   and @"guess"@ with their respective argument types.
type GameStateMachineSchema =
    BlockchainActions
        .\/ Endpoint "lock" LockArgs
        .\/ Endpoint "guess" GuessArgs

data GameError =
    GameContractError ContractError
    | GameStateMachineError (SM.SMContractError GameState GameInput)
    deriving (Show)

-- | Top-level contract, exposing both endpoints.
contract :: Contract GameStateMachineSchema GameError ()
contract = (lock <|> guess) >> contract

-- | State of the guessing game
data GameState =
    Initialised HashedString
    -- ^ Initial state. In this state only the 'ForgeTokens' action is allowed.
    | Locked TokenName HashedString
    -- ^ Funds have been locked. In this state only the 'Guess' action is
    --   allowed.
    deriving (Show)

instance Eq GameState where
    {-# INLINABLE (==) #-}
    (Initialised (HashedString s)) == (Initialised (HashedString s')) = s == s'
    (Locked (V.TokenName n) (HashedString s)) == (Locked (V.TokenName n') (HashedString s')) = s == s' && n == n'
    _ == _ = traceIfFalseH "states not equal" False

-- | Check whether a 'ClearString' is the preimage of a
--   'HashedString'
checkGuess :: HashedString -> ClearString -> Bool
checkGuess (HashedString actual) (ClearString gss) = actual == (sha2_256 gss)

-- | Inputs (actions)
data GameInput =
      ForgeToken TokenName
    -- ^ Forge the "guess" token
    | Guess ClearString HashedString Value
    -- ^ Make a guess, extract the funds, and lock the remaining funds using a
    --   new secret word.
    deriving (Show)

{-# INLINABLE step #-}
step :: GameState -> GameInput -> Maybe GameState
step state input = case (state, input) of
    (Initialised s, ForgeToken tn) -> Just $ Locked tn s
    (Locked tn _, Guess _ nextSecret _) -> Just $ Locked tn nextSecret
    _ -> Nothing

{-# INLINABLE check #-}
check :: GameState -> GameInput -> PendingTx -> Bool
check state input ptx = case (state, input) of
    (Initialised _, ForgeToken tn) -> checkForge (tokenVal tn)
    (Locked tn currentSecret, Guess theGuess _ _) ->
        checkGuess currentSecret theGuess
            && tokenPresent tn
            && checkForge zero
    _ -> False
    where
        -- | Given a 'TokeName', get the value that contains
        --   exactly one token of that name in the contract's
        --   currency.
        tokenVal :: TokenName -> V.Value
        tokenVal tn =
            let ownSymbol = Validation.ownCurrencySymbol ptx
            in V.singleton ownSymbol tn 1
        -- | Check whether the token that was forged at the beginning of the
        --   contract is present in the pending transaction
        tokenPresent :: TokenName -> Bool
        tokenPresent tn =
            let vSpent = Validation.valueSpent ptx
            in  V.geq vSpent (tokenVal tn)
        -- | Check whether the value forged by the  pending transaction 'p' is
        --   equal to the argument.
        checkForge :: Value -> Bool
        checkForge vl = vl == (Validation.pendingTxForge ptx)

{-# INLINABLE machine #-}
machine :: SM.StateMachine GameState GameInput
machine = SM.StateMachine step check (const False)

{-# INLINABLE mkValidator #-}
mkValidator :: Scripts.ValidatorType (SM.StateMachine GameState GameInput)
mkValidator = SM.mkValidator (SM.StateMachine step check (const False))

scriptInstance :: Scripts.ScriptInstance (SM.StateMachine GameState GameInput)
scriptInstance = Scripts.validator @(SM.StateMachine GameState GameInput)
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @GameState @GameInput

-- | The 'SM.StateMachineInstance' of the game state machine contract. It uses
--   the functions in 'Language.PlutusTx.StateMachine' to generate a validator
--   script based on the functions 'step' and 'check' we defined above.
machineInstance :: SM.StateMachineInstance GameState GameInput
machineInstance = SM.StateMachineInstance machine scriptInstance

-- | Allocate the funds for each transition.
allocate :: GameState -> GameInput -> Value -> ValueAllocation
allocate (Initialised _) (ForgeToken _) currentVal =
    ValueAllocation
        { vaOwnAddress    = currentVal
        -- use 'Tx.forgeValue' to ensure that the transaction forges
        -- the token.
        , vaOtherPayments = Tx.forgeValue gameTokenVal
        }
allocate (Locked _ _) (Guess _ _ takenOut) currentVal =
    ValueAllocation
        { vaOwnAddress = currentVal - takenOut
        -- use 'Tx.moveValue' to ensure that the transaction includes
        -- the token. When the transaction is submitted the wallet will
        -- add the token as an input and as an output.
        , vaOtherPayments = Tx.moveValue gameTokenVal
        }
allocate _ _ _ = Haskell.mempty

client :: SM.StateMachineClient GameState GameInput
client = SM.mkStateMachineClient machineInstance allocate

-- | Name of the token that needs to be present when making a guess.
gameToken :: TokenName
gameToken = "guess"

-- | The 'Value' forged by the 'curValidator' contract.
gameTokenVal :: Value
gameTokenVal =
    let
        -- see note [Obtaining the currency symbol]
        cur = scriptCurrencySymbol (Scripts.validatorScript scriptInstance)
    in
        V.singleton cur gameToken 1

-- | The @"guess"@ endpoint.
guess ::
    ( AsContractError e
    , AsSMContractError e GameState GameInput
    )
    => Contract GameStateMachineSchema e ()
guess = do
    GuessArgs{guessArgsOldSecret,guessArgsNewSecret, guessArgsValueTakenOut} <- endpoint @"guess"

    let guessedSecret = ClearString (C.pack guessArgsOldSecret)
        newSecret     = HashedString (sha2_256 (C.pack guessArgsNewSecret))

    void (SM.runStep client (Guess guessedSecret newSecret guessArgsValueTakenOut))

lock ::
    ( AsContractError e
    , AsSMContractError e GameState GameInput
    )
    => Contract GameStateMachineSchema e ()
lock = do
    LockArgs{lockArgsSecret, lockArgsValue} <- endpoint @"lock"
    let secret = HashedString (sha2_256 (C.pack lockArgsSecret))
    _ <- SM.runInitialise client (Initialised secret) lockArgsValue
    void (SM.runStep client (ForgeToken gameToken))

PlutusTx.makeIsData ''GameState
PlutusTx.makeLift ''GameState
PlutusTx.makeIsData ''GameInput
PlutusTx.makeLift ''GameInput
makeClassyPrisms ''GameError

instance AsContractError GameError where
    _ContractError = _GameContractError

instance AsSMContractError GameError GameState GameInput where
    _SMContractError = _GameStateMachineError

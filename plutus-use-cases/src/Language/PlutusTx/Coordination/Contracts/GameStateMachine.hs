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

import           Control.Monad                (void)
import           Data.Text                    (Text)
import qualified Language.PlutusTx            as PlutusTx
import           Language.PlutusTx.Prelude    hiding (check, Applicative (..), (<>))
import           Ledger                       hiding (to)
import           Ledger.Value                 (TokenName)
import qualified Ledger.Value                 as V
import qualified Ledger.Validation            as Validation
import qualified Ledger.Typed.Scripts         as Scripts

import qualified Data.ByteString.Lazy.Char8   as C

import qualified Language.PlutusTx.StateMachine as SM
import           Language.PlutusTx.StateMachine ()

import           Language.Plutus.Contract
import qualified Language.Plutus.Contract.Tx as Tx
import           Prelude ((<>))

newtype HashedString = HashedString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString deriving newtype PlutusTx.IsData

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
        , guessArgsValueLocked :: Value
        -- ^ How much to put back into the contract
        } deriving Show

-- | The schema of the contract. It consists of the usual
--   'BlockchainActions' plus the two endpoints @"lock"@
--   and @"guess"@ with their respective argument types.
type GameStateMachineSchema =
    BlockchainActions
        .\/ Endpoint "lock" LockArgs
        .\/ Endpoint "guess" GuessArgs

-- | Top-level contract, exposing both endpoints.
contract :: Contract GameStateMachineSchema Text ()
contract = (lock <|> guess) >> contract

-- | State of the guessing game
data GameState =
    Initialised HashedString
    -- ^ Initial state. In this state only the 'ForgeTokens' action is allowed.
    | Locked TokenName HashedString
    -- ^ Funds have been locked. In this state only the 'Guess' action is
    --   allowed.

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
    | Guess ClearString HashedString
    -- ^ Make a guess and lock the remaining funds using a new secret word.

{-# INLINABLE step #-}
step :: GameState -> GameInput -> Maybe GameState
step state input = case (state, input) of
    (Initialised s, ForgeToken tn) -> Just $ Locked tn s
    (Locked tn _, Guess _ nextSecret) -> Just $ Locked tn nextSecret
    _ -> Nothing

{-# INLINABLE check #-}
check :: GameState -> GameInput -> PendingTx -> Bool
check state input ptx = case (state, input) of
    (Initialised _, ForgeToken tn) -> checkForge (tokenVal tn)
    (Locked tn currentSecret, Guess theGuess _) -> checkGuess currentSecret theGuess && tokenPresent tn && checkForge zero
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
scriptInstance = Scripts.Validator @(SM.StateMachine GameState GameInput)
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @GameState @GameInput

-- | The 'SM.StateMachineInstance' of the game state machine contract. It uses
--   the functions in 'Language.PlutusTx.StateMachine' to generate a validator
--   script based on the functions 'step' and 'check' we defined above.
machineInstance :: SM.StateMachineInstance GameState GameInput
machineInstance = SM.StateMachineInstance machine scriptInstance

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
guess :: AsContractError e => Contract GameStateMachineSchema e ()
guess = do
    GuessArgs{guessArgsOldSecret,guessArgsNewSecret, guessArgsValueLocked} <- endpoint @"guess"

    let guessedSecret = ClearString (C.pack guessArgsOldSecret)
        newSecret     = HashedString (sha2_256 (C.pack guessArgsNewSecret))
        input         = Guess guessedSecret newSecret
        newState      = Locked gameToken newSecret
        ds            = DataScript $ PlutusTx.toData newState
        redeemer      = RedeemerScript $ PlutusTx.toData input
        addr          = Scripts.scriptAddress scriptInstance

    -- We need to know the unspent outputs at the contract address, and a public
    -- key that we can send the token to. 
    utxo <- utxoAt addr
    pubKey <- ownPubKey

    -- The transaction has three parts which are joined together using the 
    -- '<>' semigroup operator.
    let tx = 
             -- part 1: Spend the outputs that are currently at the address
            Tx.collectFromScript
                utxo 
                (Scripts.validatorScript scriptInstance)
                redeemer

             -- part 2: Lock the remaining funds in the contract with the new 
             -- state 'ds'
             <> Tx.payToScript guessArgsValueLocked addr ds 

             -- part 3: Pay the token to our own public key (this is a no-op on 
             -- the wallet's balance but it ensures that the token is present 
             -- in the transaction)
             <> Tx.payToPubKey gameTokenVal pubKey 
    void $ submitTx tx

lock :: AsContractError e => Contract GameStateMachineSchema e ()
lock = do
    LockArgs{lockArgsSecret, lockArgsValue} <- endpoint @"lock"
    let secret            = HashedString (sha2_256 (C.pack lockArgsSecret))
        addr              = Scripts.scriptAddress scriptInstance
        initialDataScript = DataScript $ PlutusTx.toData (Initialised secret)
    
    -- 1. Create a transaction output with the value and the secret and
    --    wait until it is confirmed.
    let tx1 = Tx.payToScript lockArgsValue addr initialDataScript
    _ <- submitTxConfirmed tx1

    -- Get the current utxo set at the contract address. This consists of
    -- exactly the one output that we added earlier (unless someone else
    -- is playing the game at the same time, in which case it would be ruined
    -- for everybody.)
    utxo <- utxoAt addr
    let input         = ForgeToken gameToken
        newState      = Locked gameToken secret
        redeemer      = RedeemerScript $ PlutusTx.toData input
        newDataScript = DataScript $ PlutusTx.toData newState
    
    -- 2. The state of the contract is now 'Initialised'. To transition to
    --    the 'Locked' state we need to run the 'Forge' action. The transaction
    --    has three parts:
    let tx2 = 
             -- 1. Spend the outputs at the contract address
             Tx.collectFromScript 
                    utxo 
                    (Scripts.validatorScript scriptInstance)
                    redeemer
             -- 2. Lock the funds at the contract address with the new state
             <> Tx.payToScript lockArgsValue addr newDataScript

             -- 3. Forge the token.
             <> Tx.forgeValue gameTokenVal

    submitTxConfirmed tx2

PlutusTx.makeIsData ''GameState
PlutusTx.makeLift ''GameState
PlutusTx.makeIsData ''GameInput
PlutusTx.makeLift ''GameInput
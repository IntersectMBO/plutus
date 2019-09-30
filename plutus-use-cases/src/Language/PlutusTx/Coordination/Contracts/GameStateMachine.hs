{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | A guessing game that
--
--   * Uses a state machine to keep track of the current secret word
--   * Uses a token to keep track of who is allowed to make a guess
--

module Language.PlutusTx.Coordination.Contracts.GameStateMachine(
      startGame
    , guess
    , lock
    , scriptInstance
    , gameTokenVal
    , mkValidator
    ) where

import           Control.Applicative          (Applicative (..))
import qualified Data.Map                     as Map
import           Data.Maybe                   (maybeToList)
import qualified Data.Set                     as Set
import qualified Data.Text                    as Text
import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Applicative as PlutusTx
import           Language.PlutusTx.Prelude    hiding (check, Applicative (..))
import           Ledger                       hiding (to)
import           Ledger.Value                 (TokenName)
import qualified Ledger.Value                 as V
import qualified Ledger.Validation            as Validation
import qualified Ledger.Typed.Scripts         as Scripts
import           Wallet
import qualified Wallet                       as WAPI

import qualified Data.ByteString.Lazy.Char8   as C

import qualified Language.PlutusTx.StateMachine as SM
import           Language.PlutusTx.StateMachine ()

newtype HashedString = HashedString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''ClearString

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

instance PlutusTx.IsData GameState where
    toData (Initialised s) = PlutusTx.Constr 0 [PlutusTx.toData s]
    toData (Locked n s) = PlutusTx.Constr 1 [PlutusTx.toData n, PlutusTx.toData s]
    {-# INLINABLE fromData #-}
    fromData (PlutusTx.Constr i [s]) | i == 0 = Initialised <$> PlutusTx.fromData s
    fromData (PlutusTx.Constr i [n, s]) | i == 1 = Locked <$> PlutusTx.fromData n PlutusTx.<*> PlutusTx.fromData s
    fromData _ = Nothing

PlutusTx.makeLift ''GameState

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

instance PlutusTx.IsData GameInput where
    toData (ForgeToken n) = PlutusTx.Constr 0 [PlutusTx.toData n]
    toData (Guess g h) = PlutusTx.Constr 1 [PlutusTx.toData g, PlutusTx.toData h]
    {-# INLINABLE fromData #-}
    fromData (PlutusTx.Constr i [n]) | i == 0 = ForgeToken <$> PlutusTx.fromData n
    fromData (PlutusTx.Constr i [g, h]) | i == 1 = Guess <$> PlutusTx.fromData g PlutusTx.<*> PlutusTx.fromData h
    fromData _ = Nothing

PlutusTx.makeLift ''GameInput

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

machineInstance :: SM.StateMachineInstance GameState GameInput
machineInstance = SM.StateMachineInstance machine scriptInstance

gameToken :: TokenName
gameToken = "guess"

-- | The 'Value' forged by the 'curValidator' contract
gameTokenVal :: Value
gameTokenVal =
    let
        -- see note [Obtaining the currency symbol]
        cur = plcCurrencySymbol (Scripts.scriptAddress scriptInstance)
    in
        V.singleton cur gameToken 1

-- | Make a guess, take out some funds, and lock the remaining 'Value' with a new
--   secret
guess ::
    (WalletAPI m, WalletDiagnostics m)
    => String
    -- ^ The guess
    -> String
    -- ^ A new secret
    -> Value
    -- ^ How much ada to take out
    -> Value
    -- ^ How much to put back into the contract
    -> m ()
guess gss new keepVal restVal = do

    let addr = Scripts.scriptAddress scriptInstance
        guessedSecret = ClearString (C.pack gss)
        newSecret = HashedString (plcSHA2_256 (C.pack new))
        input = Guess guessedSecret newSecret
        newState = Locked gameToken newSecret
        redeemer = RedeemerScript $ PlutusTx.toData input
    ins <- WAPI.spendScriptOutputs addr (Scripts.validatorScript scriptInstance) redeemer
    ownOutput <- WAPI.ownPubKeyTxOut (keepVal <> gameTokenVal)

    let scriptOut = scriptTxOut restVal (Scripts.validatorScript scriptInstance) (DataScript $ PlutusTx.toData newState)

    (i, own) <- createPaymentWithChange gameTokenVal

    let tx = Ledger.Tx
                { txInputs = Set.union i (Set.fromList $ fmap fst ins)
                , txOutputs = [ownOutput, scriptOut] ++ maybeToList own
                , txForge = zero
                , txFee   = zero
                , txValidRange = defaultSlotRange
                , txSignatures = Map.empty
                }

    WAPI.signTxAndSubmit_ tx

-- | Lock some funds in the guessing game. Produces the token that is required
--   when submitting a guess.
lock :: (WalletAPI m, WalletDiagnostics m) => String -> Value -> m ()
lock initialWord vl = do
    let secret = HashedString (plcSHA2_256 (C.pack initialWord))
        addr = Scripts.scriptAddress scriptInstance
        state = Initialised secret
        ds   = DataScript $ PlutusTx.toData state

    -- 1. Create a transaction output with the value and the secret
    payToScript_ defaultSlotRange addr vl ds

    -- 2. Define a trigger that fires when the first transaction (1.) is
    --    placed on the chain.
    let trg1        = fundsAtAddressGtT addr zero

    -- 3. Define a forge_ action that creates the token by and puts the contract
    --    into its new state.
    let forge :: (WalletAPI m, WalletDiagnostics m) => m ()
        forge = do
            ownOutput <- WAPI.ownPubKeyTxOut gameTokenVal
            let input = ForgeToken gameToken
                newState = Locked gameToken secret
                redeemer = RedeemerScript $ PlutusTx.toData input
                scriptOut = scriptTxOut vl (Scripts.validatorScript scriptInstance) (DataScript $ PlutusTx.toData newState)
            ins <- WAPI.spendScriptOutputs addr (Scripts.validatorScript scriptInstance) redeemer

            let tx = Ledger.Tx
                        { txInputs = Set.fromList (fmap fst ins)
                        , txOutputs = [ownOutput, scriptOut]
                        , txForge = gameTokenVal
                        , txFee   = zero
                        , txValidRange = defaultSlotRange
                        , txSignatures = Map.empty
                        }

            WAPI.logMsg $ Text.pack $ "The forging transaction is: " <> show (Ledger.hashTx tx)
            WAPI.signTxAndSubmit_ tx


    registerOnce trg1 (EventHandler $ const forge)
    pure ()

-- | Tell the wallet to start watching the address of the game script
startGame :: WalletAPI m => m ()
startGame = startWatching (Scripts.scriptAddress scriptInstance)

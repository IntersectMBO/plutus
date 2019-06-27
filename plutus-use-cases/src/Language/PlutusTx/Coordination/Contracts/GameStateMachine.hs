{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
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
    , gameTokenVal
    , gameValidator
    , mkValidator
    ) where

import qualified Data.Map                     as Map
import           Data.Maybe                   (maybeToList)
import qualified Data.Set                     as Set
import qualified Data.Text                    as Text
import qualified Language.PlutusTx            as PlutusTx
import           Language.PlutusTx.Prelude
import           Ledger                       hiding (to)
import qualified Ledger.Ada                   as Ada
import           Ledger.Value                 (TokenName)
import qualified Ledger.Value                 as V
import qualified Ledger.Validation            as Validation
import           Wallet
import qualified Wallet                       as WAPI

import qualified Data.ByteString.Lazy.Char8   as C

import qualified Language.PlutusTx.StateMachine as SM
import           Language.PlutusTx.StateMachine ()

import           Language.PlutusTx.Coordination.Contracts.GameStateMachine.Types

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

PlutusTx.makeLift ''GameInput

mkValidator :: (GameState, Maybe GameInput) -> (GameState, Maybe GameInput) -> PendingTx -> Bool
mkValidator ds vs p =
    let

        -- | Given a 'TokeName', get the value that contains
        --   exactly one token of that name in the contract's
        --   currency.
        tokenVal :: TokenName -> V.Value
        tokenVal tn =
            let ownSymbol = Validation.ownCurrencySymbol p
            in V.singleton ownSymbol tn 1

        -- | Check whether the token that was forged at the beginning of the
        --   contract is present in the pending transaction
        tokenPresent :: TokenName -> Bool
        tokenPresent tn =
            let vSpent = Validation.valueSpent p
            in  V.geq vSpent (tokenVal tn)

        -- | Check whether the value forged by the  pending transaction 'p' is
        --   equal to the argument.
        checkForge :: Value -> Bool
        checkForge vl = vl == (Validation.pendingTxForge p)

        -- | The SM.transition function of the game's state machine
        trans :: GameState -> GameInput -> GameState
        trans (Initialised s) (ForgeToken tn) =
            if checkForge (tokenVal tn)
            then Locked tn s
            else error ()
        trans (Locked tn currentSecret) (Guess theGuess nextSecret) =
            if checkGuess currentSecret theGuess && tokenPresent tn && checkForge V.zero
            then Locked tn nextSecret
            else error ()
        trans _ _ = traceErrorH "Invalid SM.transition"

        sm = SM.StateMachine trans

    in SM.mkValidator sm ds vs p

gameValidator :: ValidatorScript
gameValidator = ValidatorScript $$(Ledger.compileScript [|| mkValidator ||])

gameToken :: TokenName
gameToken = "guess"

-- | The 'Value' forged by the 'curValidator' contract
gameTokenVal :: Value
gameTokenVal =
    let
        -- see note [Obtaining the currency symbol]
        cur = plcCurrencySymbol (Ledger.scriptAddress gameValidator)
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
guess gss newSecret keepVal restVal = do

    let clear = ClearString (C.pack gss)
        addr = Ledger.scriptAddress gameValidator
        scr   = HashedString (plcSHA2_256 (C.pack newSecret))
    let step = SM.transition (Locked gameToken scr) (Guess clear scr)
    ins <- WAPI.spendScriptOutputs addr gameValidator (RedeemerScript (Ledger.lifted step))
    ownOutput <- WAPI.ownPubKeyTxOut (keepVal <> gameTokenVal)

    let scriptOut = scriptTxOut restVal gameValidator (DataScript (Ledger.lifted step))

    (i, own) <- createPaymentWithChange gameTokenVal

    let tx = Ledger.Tx
                { txInputs = Set.union i (Set.fromList $ fmap fst ins)
                , txOutputs = [ownOutput, scriptOut] ++ maybeToList own
                , txForge = V.zero
                , txFee   = Ada.zero
                , txValidRange = defaultSlotRange
                , txSignatures = Map.empty
                }

    WAPI.signTxAndSubmit_ tx

-- | Lock some funds in the guessing game. Produces the token that is required
--   when submitting a guess.
lock :: (WalletAPI m, WalletDiagnostics m) => String -> Value -> m ()
lock initialWord vl = do
    let secret = HashedString (plcSHA2_256 (C.pack initialWord))
        addr = Ledger.scriptAddress gameValidator
        state = SM.initialState @GameState @GameInput (Initialised secret)
        ds   = DataScript (Ledger.lifted state)

    -- 1. Create a transaction output with the value and the secret
    payToScript_ defaultSlotRange addr vl ds

    -- 2. Define a trigger that fires when the first transaction (1.) is
    --    placed on the chain.
    let trg1        = fundsAtAddressGtT addr V.zero

    -- 3. Define a forge_ action that creates the token by and puts the contract
    --    into its new state.
    let forge :: (WalletAPI m, WalletDiagnostics m) => m ()
        forge = do
            ownOutput <- WAPI.ownPubKeyTxOut gameTokenVal
            let step = SM.transition (Locked gameToken secret) (ForgeToken gameToken)
                scriptOut = scriptTxOut vl gameValidator (DataScript (Ledger.lifted step))
                redeemer = RedeemerScript (Ledger.lifted step)
            ins <- WAPI.spendScriptOutputs addr gameValidator redeemer

            let tx = Ledger.Tx
                        { txInputs = Set.fromList (fmap fst ins)
                        , txOutputs = [ownOutput, scriptOut]
                        , txForge = gameTokenVal
                        , txFee   = Ada.zero
                        , txValidRange = defaultSlotRange
                        , txSignatures = Map.empty
                        }

            WAPI.logMsg $ Text.pack $ "The forging transaction is: " <> show (Ledger.hashTx tx)
            WAPI.signTxAndSubmit_ tx


    registerOnce trg1 (EventHandler $ const forge)
    pure ()

-- | Tell the wallet to start watching the address of the game script
startGame :: WalletAPI m => m ()
startGame = startWatching (Ledger.scriptAddress gameValidator)

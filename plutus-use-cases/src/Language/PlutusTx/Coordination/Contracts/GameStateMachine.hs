{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
{-# OPTIONS_GHC -O0 #-}
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
    ) where

import qualified Data.Map                     as Map
import           Data.Maybe                   (maybeToList)
import qualified Data.Set                     as Set
import qualified Data.Text                    as Text
import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Prelude    as P
import           Ledger                       hiding (to)
import qualified Ledger.Ada                   as Ada
import           Ledger.Value                 (TokenName)
import qualified Ledger.Value.TH              as V
import qualified Ledger.Validation            as Validation
import           Wallet
import qualified Wallet                       as WAPI

import qualified Data.ByteString.Lazy.Char8   as C

import Language.PlutusTx.Coordination.Contracts.GameStateMachine.Stage0

data HashedString = HashedString (P.SizedByteString 32)

PlutusTx.makeLift ''HashedString

data ClearString = ClearString (P.SizedByteString 32)

PlutusTx.makeLift ''ClearString

-- | State of the guessing game
data GameState = 
    Initialised HashedString
    -- ^ Initial state. In this state only the 'ForgeTokens' action is allowed.
    | Locked TokenName HashedString
    -- ^ Funds have been locked. In this state only the 'Guess' action is 
    --   allowed.

PlutusTx.makeLift ''GameState

-- | Inputs (actions)
data GameInput =
      ForgeToken TokenName
    -- ^ Forge the "guess" token
    | Guess ClearString HashedString
    -- ^ Make a guess and lock the remaining funds using a new secret word.

PlutusTx.makeLift ''GameInput

gameValidator :: ValidatorScript
gameValidator = ValidatorScript ($$(Ledger.compileScript [||
    \(ds :: (GameState, Maybe GameInput)) (vs :: (GameState, Maybe GameInput)) (p :: PendingTx) ->

    let 

        -- | Check whether a 'ClearString' is the preimage of a
        --   'HashedString'
        checkGuess :: HashedString -> ClearString -> Bool
        checkGuess (HashedString actual) (ClearString gss) =
            $$(P.equalsByteString) actual ($$(P.sha2_256) gss)
            
        -- | Given a 'TokeName', get the value that contains 
        --   exactly one token of that name
        tokenVal :: TokenName -> V.Value
        tokenVal tn = 
            let ownSymbol = $$(Validation.ownCurrencySymbol) p
            in $$(V.singleton) ownSymbol tn 1

        -- | Check whether the token that was forged at the beginning of the
        --   contract is present in the pending transaction
        tokenPresent :: TokenName -> Bool
        tokenPresent tn =
            let vSpent = $$(Validation.valueSpent) p
            in  $$(V.geq) vSpent (tokenVal tn)

        -- | Check whether the value forged by the  pending transaction 'p' is
        --   equal to the argument.
        checkForge :: Value -> Bool
        checkForge vl = $$(V.eq) vl ($$(Validation.valueForged) p)
        
        -- | Equality of 'GameState' valzes.
        stateEq :: GameState -> GameState -> Bool
        stateEq (Initialised (HashedString s)) (Initialised (HashedString s')) =
            $$(P.equalsByteString) s s'
        stateEq (Locked (V.TokenName n) (HashedString s)) (Locked (V.TokenName n') (HashedString s')) =
            $$(P.and) ($$(P.equalsByteString) s s') ($$(P.equalsByteString) n n')
        stateEq _ _ = $$(P.traceIfFalseH) "states not equal" False

        -- | The transition function of the game's state machine
        trans :: GameState -> GameInput -> GameState
        trans (Initialised s) (ForgeToken tn) =
            if checkForge (tokenVal tn)
            then Locked tn s 
            else $$(P.error) ()
        trans (Locked tn currentSecret) (Guess theGuess nextSecret) =
            if $$(P.and) 
                (checkGuess currentSecret theGuess)
                ($$(P.and) (tokenPresent tn) (checkForge $$(V.zero)))
            then Locked tn nextSecret
            else $$(P.error) ()
        trans _ _ = $$(P.traceH) "Invalid transition" ($$(P.error) ())

        sm = StateMachine trans stateEq

    in
        $$(mkValidator) sm ds vs p

    ||]))

gameToken :: TokenName
gameToken = "guess"

-- | The 'Value' forged by the 'curValidator' contract
gameTokenVal :: Value
gameTokenVal =
    let
        -- see note [Obtaining the currency symbol]
        cur = plcCurrencySymbol (Ledger.scriptAddress gameValidator)
    in
        $$(V.singleton) cur gameToken 1

-- | Make a guess, take out some funds, and lock the remaining 'Ada' with a new 
--   secret
guess :: 
    (WalletAPI m, WalletDiagnostics m) 
    => String 
    -- ^ The guess
    -> String 
    -- ^ A new secret
    -> Ada 
    -- ^ How much ada to take out
    -> Ada 
    -- ^ How much to put back into the contract
    -> m ()
guess gss newSecret keepAda restAda = do

    let clear = ClearString (P.SizedByteString (C.pack gss))
        addr = Ledger.scriptAddress gameValidator
        scr   = HashedString (plcSHA2_256 (P.SizedByteString (C.pack newSecret)))
    let step = transition (Locked gameToken scr) (Guess clear scr)
    ins <- WAPI.spendScriptOutputs addr gameValidator (RedeemerScript (Ledger.lifted step))
    ownOutput <- WAPI.ownPubKeyTxOut (Ada.toValue keepAda <> gameTokenVal)

    let scriptOut = scriptTxOut (Ada.toValue restAda) gameValidator (DataScript (Ledger.lifted step))

    (i, own) <- createPaymentWithChange gameTokenVal

    let tx = Ledger.Tx
                { txInputs = Set.union i (Set.fromList ins)
                , txOutputs = [ownOutput, scriptOut] ++ maybeToList own
                , txForge = $$(V.zero)
                , txFee   = Ada.zero
                , txValidRange = defaultSlotRange
                , txSignatures = Map.empty
                }

    WAPI.signTxAndSubmit_ tx

-- | Lock some funds in the guessing game. Produces the token that is required 
--   when submitting a guess.
lock :: (WalletAPI m, WalletDiagnostics m) => String -> Ada -> m ()
lock initialWord adaVl = do
    let secret = HashedString (plcSHA2_256 (P.SizedByteString (C.pack initialWord)))
        addr = Ledger.scriptAddress gameValidator
        state = initialState @GameState @GameInput (Initialised secret)
        ds   = DataScript (Ledger.lifted state)

    -- 1. Create a transaction output with the value and the secret
    payToScript_ defaultSlotRange addr (Ada.toValue adaVl) ds

    -- 2. Define a trigger that fires when the first transaction (1.) is
    --    placed on the chain.
    let oneOrMore   = WAPI.intervalFrom $ Ada.adaValueOf 1
        trg1        = fundsAtAddressT addr oneOrMore

    -- 3. Define a forge_ action that creates the token by and puts the contract
    --    into its new state.
    let forge :: (WalletAPI m, WalletDiagnostics m) => m ()
        forge = do
            ownOutput <- WAPI.ownPubKeyTxOut gameTokenVal
            let step = transition (Locked gameToken secret) (ForgeToken gameToken)
                scriptOut = scriptTxOut (Ada.toValue adaVl) gameValidator (DataScript (Ledger.lifted step))
                redeemer = RedeemerScript (Ledger.lifted step)
            ins <- WAPI.spendScriptOutputs addr gameValidator redeemer

            let tx = Ledger.Tx
                        { txInputs = Set.fromList ins
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

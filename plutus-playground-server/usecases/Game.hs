{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}

module Game where

-- TRIM TO HERE
-- A game with two players. Player 1 thinks of a secret word
-- and uses its hash, and the game validator script, to lock
-- some funds (the prize) in a pay-to-script transaction output.
-- Player 2 guesses the word by attempting to spend the transaction
-- output. If the guess is correct, the validator script releases the funds.
-- If it isn't, the funds stay locked.
import           Control.Applicative        ((<|>))
import           Control.Monad              (void)
import qualified Data.ByteString.Lazy.Char8 as C
import           IOTS                       (IotsType)
import qualified Language.PlutusTx          as PlutusTx
import           Language.PlutusTx.Prelude  hiding (pure, (<$>))
import           Ledger                     (Address, DataValue (DataValue), PendingTx,
                                             RedeemerValue (RedeemerValue), Validator, mkValidatorScript, scriptAddress)
import           Ledger.Ada                 (Ada)
import qualified Ledger.Ada                 as Ada
import           Ledger.Typed.Scripts       (wrapValidator)
import           Language.Plutus.Contract.Tx
import           Playground.Contract
import           Prelude                    (Eq, Ord, Show)

------------------------------------------------------------

newtype HashedString = HashedString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''ClearString

type GameSchema =
    BlockchainActions
        .\/ Endpoint "lock" LockParams
        .\/ Endpoint "guess" GuessParams

-- | The validator (datavalue -> redeemer -> PendingTx -> Bool)
validateGuess :: HashedString -> ClearString -> PendingTx -> Bool
validateGuess (HashedString actual) (ClearString guess') _ = actual == sha2_256 guess'

-- | The validator script of the game.
gameValidator :: Validator
gameValidator = Ledger.mkValidatorScript $$(PlutusTx.compile [|| validator ||])
    where validator = wrapValidator validateGuess

-- create a data script for the guessing game by hashing the string
-- and lifting the hash to its on-chain representation
gameDataScript :: String -> DataValue
gameDataScript =
    Ledger.DataValue . PlutusTx.toData . HashedString . sha2_256 . C.pack

-- create a redeemer script for the guessing game by lifting the
-- string to its on-chain representation
gameRedeemerValue :: String -> RedeemerValue
gameRedeemerValue =
    Ledger.RedeemerValue . PlutusTx.toData . ClearString . C.pack

-- | The address of the game (the hash of its validator script)
gameAddress :: Address
gameAddress = Ledger.scriptAddress gameValidator

-- | Parameters for the "lock" endpoint
data LockParams = LockParams
    { secretWord :: String
    , amount     :: Ada
    }
    deriving stock (Prelude.Eq, Prelude.Ord, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, IotsType, ToSchema, ToArgument)

--  | Parameters for the "guess" endpoint
newtype GuessParams = GuessParams
    { guessWord :: String
    }
    deriving stock (Prelude.Eq, Prelude.Ord, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, IotsType, ToSchema, ToArgument)

-- | The "guess" contract endpoint. See note [Contract endpoints]
guess :: AsContractError e => Contract GameSchema e ()
guess = do
    GuessParams theGuess <- endpoint @"guess" @GuessParams
    mp <- utxoAt gameAddress
    let redeemer = gameRedeemerValue theGuess
        tx       = collectFromScript mp gameValidator redeemer
    void (submitTx tx)

-- | The "lock" contract endpoint. See note [Contract endpoints]
lock :: AsContractError e => Contract GameSchema e ()
lock = do
    LockParams secret amt <- endpoint @"lock" @LockParams
    let
        vl         = Ada.toValue amt
        dataValue = gameDataScript secret
        tx         = payToScript vl (Ledger.scriptAddress gameValidator) dataValue
    void (submitTx tx)

game :: AsContractError e => Contract GameSchema e ()
game = guess <|> lock

{- Note [Contract endpoints]

A contract endpoint is a function that uses the wallet API to interact with the
blockchain. We can look at contract endpoints from two different points of view.

1. Contract users

Contract endpoints are the visible interface of the contract. They provide a
UI (HTML form) for entering the parameters of the actions we may take as part
of the contract.

2. Contract authors

As contract authors we define endpoints as functions that return a value of
type 'MockWallet ()'. This type indicates that the function uses the wallet API
to produce and spend transaction outputs on the blockchain.

Endpoints can have any number of parameters: 'lock' has two
parameters, 'guess' has one and 'startGame' has none. For each endpoint we
include a call to 'mkFunction' at the end of the contract definition. This
causes the Haskell compiler to generate a schema for the endpoint. The Plutus
Playground then uses this schema to present an HTML form to the user where the
parameters can be entered.

-}

endpoints :: AsContractError e => Contract GameSchema e ()
endpoints = game

mkSchemaDefinitions ''GameSchema

myCurrency :: KnownCurrency
myCurrency = KnownCurrency "b0b0" "MyCurrency" ( "USDToken" :| ["EURToken"])
$(mkKnownCurrencies ['myCurrency])

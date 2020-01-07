{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | A guessing game
module Language.PlutusTx.Coordination.Contracts.Game
    ( lock
    , guess
    , game
    , GameSchema
    , GuessParams(..)
    , LockParams(..)
    -- * Scripts
    , gameValidator
    , hashString
    , clearString
    -- * Address
    , gameAddress
    , validateGuess
    -- * Traces
    , guessTrace
    , guessWrongTrace
    , lockTrace
    ) where

import Control.Monad (void)
import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import IOTS (IotsType)
import Language.Plutus.Contract
import Language.Plutus.Contract.Schema ()
import Language.Plutus.Contract.Trace (ContractTrace, MonadEmulator, TraceError)
import qualified Language.Plutus.Contract.Trace as Trace
import qualified Language.PlutusTx as PlutusTx
import Language.PlutusTx.Prelude
import qualified Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Ledger
    ( Address
    , PendingTx
    , Validator
    , Value
    )
import Schema (ToSchema, ToArgument)

import qualified Ledger as Ledger
import qualified Ledger.Ada as Ada

import qualified Data.ByteString.Lazy.Char8 as C
import qualified Prelude

newtype HashedString = HashedString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''ClearString

type GameSchema =
    BlockchainActions
        .\/ Endpoint "lock" LockParams
        .\/ Endpoint "guess" GuessParams

-- | The validation function (DataValue -> RedeemerValue -> PendingTx -> Bool)
validateGuess :: HashedString -> ClearString -> PendingTx -> Bool
validateGuess (HashedString actual) (ClearString guess') _ = actual == sha2_256 guess'

-- | The validator script of the game.
gameValidator :: Validator
gameValidator = Scripts.validatorScript gameInstance

data Game
instance Scripts.ScriptType Game where
    type instance RedeemerType Game = ClearString
    type instance DataType Game = HashedString

gameInstance :: Scripts.ScriptInstance Game
gameInstance = Scripts.validator @Game
    $$(PlutusTx.compile [|| validateGuess ||])
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @HashedString @ClearString

-- create a data script for the guessing game by hashing the string
-- and lifting the hash to its on-chain representation
hashString :: String -> HashedString
hashString = HashedString . sha2_256 . C.pack

-- create a redeemer script for the guessing game by lifting the
-- string to its on-chain representation
clearString :: String -> ClearString
clearString = ClearString . C.pack

-- | The address of the game (the hash of its validator script)
gameAddress :: Address
gameAddress = Ledger.scriptAddress gameValidator

-- | Parameters for the "lock" endpoint
data LockParams = LockParams
    { secretWord :: String
    , amount     :: Value
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, IotsType, ToSchema, ToArgument)

--  | Parameters for the "guess" endpoint
newtype GuessParams = GuessParams
    { guessWord :: String
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, IotsType, ToSchema, ToArgument)

lock :: AsContractError e => Contract GameSchema e ()
lock = do
    LockParams secret amt <- endpoint @"lock" @LockParams
    let tx         = Constraints.mustPayToTheScript (hashString secret) amt
    void (submitTxConstraints gameInstance tx)

guess :: AsContractError e => Contract GameSchema e ()
guess = do
    GuessParams theGuess <- endpoint @"guess" @GuessParams
    unspentOutputs <- utxoAt gameAddress
    let redeemer = clearString theGuess
        tx       = collectFromScript unspentOutputs redeemer
    void (submitTxConstraintsSpending gameInstance unspentOutputs tx)

game :: AsContractError e => Contract GameSchema e ()
game = lock <|> guess

lockTrace
    :: ( MonadEmulator (TraceError e) m )
    => ContractTrace GameSchema e m () ()
lockTrace =
    let w1 = Trace.Wallet 1 in
    Trace.callEndpoint @"lock" w1 (LockParams "secret" (Ada.lovelaceValueOf 10))
        >> Trace.handleBlockchainEvents w1

guessTrace
    :: ( MonadEmulator (TraceError e) m )
    => ContractTrace GameSchema e m () ()
guessTrace =
    let w2 = Trace.Wallet 2 in
    lockTrace
        >> Trace.callEndpoint @"guess" w2 (GuessParams "secret")
        >> Trace.handleBlockchainEvents w2

guessWrongTrace
    :: ( MonadEmulator (TraceError e) m )
    => ContractTrace GameSchema e m () ()
guessWrongTrace =
    let w2 = Trace.Wallet 2 in
    lockTrace
        >> Trace.callEndpoint @"guess" w2 (GuessParams "SECRET")
        >> Trace.handleBlockchainEvents w2

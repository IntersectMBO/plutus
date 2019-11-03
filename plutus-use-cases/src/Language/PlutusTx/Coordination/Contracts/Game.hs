-- | A guessing game
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Language.PlutusTx.Coordination.Contracts.Game(
    lock,
    guess,
    game,
    GameSchema,
    GuessParams(..),
    LockParams(..),
    -- * Scripts
    gameValidator,
    gameDataScript,
    gameRedeemerScript,
    -- * Address
    gameAddress,
    validateGuess,
    -- * Traces
    guessTrace,
    guessWrongTrace,
    lockTrace
    ) where

import           Control.Lens                   (at, (^.))
import           Control.Monad                  (void)
import qualified Data.Aeson                     as Aeson
import qualified Data.Map                       as Map
import           Data.Maybe                     (fromMaybe)
import           GHC.Generics                   (Generic)
import           Language.Plutus.Contract.IOTS                      (IotsType)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Trace (ContractTrace, MonadEmulator)
import qualified Language.Plutus.Contract.Trace as Trace
import qualified Language.PlutusTx              as PlutusTx
import           Language.PlutusTx.Prelude
import           Ledger                         (Ada, Address, DataScript, PendingTx, RedeemerScript, ValidatorScript)
import           Ledger.Typed.Scripts           (wrapValidator)
import qualified Ledger                         as Ledger
import qualified Ledger.Ada                     as Ada
import qualified Ledger.AddressMap              as AM

import qualified Prelude

import qualified Data.ByteString.Lazy.Char8     as C

newtype HashedString = HashedString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString deriving newtype PlutusTx.IsData

PlutusTx.makeLift ''ClearString

type GameSchema =
    BlockchainActions
        .\/ Endpoint "lock" LockParams
        .\/ Endpoint "guess" GuessParams

-- | The validator (datascript -> redeemer -> PendingTx -> Bool)
validateGuess :: HashedString -> ClearString -> PendingTx -> Bool
validateGuess (HashedString actual) (ClearString guess') _ = actual == sha2_256 guess'

gameValidator :: ValidatorScript
gameValidator = Ledger.mkValidatorScript $$(PlutusTx.compile [|| validator ||])
    where validator = wrapValidator validateGuess

gameDataScript :: String -> DataScript
gameDataScript =
    Ledger.DataScript . PlutusTx.toData . HashedString . Ledger.plcSHA2_256 . C.pack

gameRedeemerScript :: String -> RedeemerScript
gameRedeemerScript =
    Ledger.RedeemerScript . PlutusTx.toData . ClearString . C.pack

gameAddress :: Address
gameAddress = Ledger.scriptAddress gameValidator

-- | Parameters for the "lock" endpoint
data LockParams = LockParams
    { secretWord :: String
    , amount     :: Ada
    }
    deriving stock (Prelude.Eq, Prelude.Ord, Prelude.Show, Generic)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON, IotsType)

--  | Parameters for the "guess" endpoint
newtype GuessParams = GuessParams
    { guessWord :: String
    }
    deriving stock (Prelude.Eq, Prelude.Ord, Prelude.Show, Generic)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON, IotsType)

guess :: Contract GameSchema e ()
guess = do
    st <- nextTransactionAt gameAddress
    let mp = AM.fromTxOutputs st
    GuessParams theGuess <- endpoint @"guess" @GuessParams
    let
        txOutputs  = Map.toList . fromMaybe Map.empty $ mp ^. at gameAddress
        redeemer   = gameRedeemerScript theGuess
        inp        = (\o -> Ledger.scriptTxIn (fst o) gameValidator redeemer) <$> txOutputs
        tx         = unbalancedTx inp []
    void (writeTx tx)

lock :: Contract GameSchema e ()
lock = do
    LockParams secret amt <- endpoint @"lock" @LockParams
    let
        vl         = Ada.toValue amt
        dataScript = gameDataScript secret
        output     = Ledger.TxOutOf gameAddress vl (Ledger.PayToScript dataScript)
        tx         = unbalancedTx [] [output]
    void (writeTx tx)

game :: Contract GameSchema e ()
game = guess <|> lock

lockTrace
    :: ( MonadEmulator e m )
    => ContractTrace GameSchema e m () ()
lockTrace =
    let w1 = Trace.Wallet 1
        w2 = Trace.Wallet 2 in
    Trace.callEndpoint @"lock" w1 (LockParams "secret" 10)
        >> Trace.notifyInterestingAddresses w2
        >> Trace.handleBlockchainEvents w1

guessTrace
    :: ( MonadEmulator e m )
    => ContractTrace GameSchema e m () ()
guessTrace =
    let w2 = Trace.Wallet 2 in
    lockTrace
        >> Trace.callEndpoint @"guess" w2 (GuessParams "secret")
        >> Trace.handleBlockchainEvents w2

guessWrongTrace
    :: ( MonadEmulator e m )
    => ContractTrace GameSchema e m () ()
guessWrongTrace =
    let w2 = Trace.Wallet 2 in
    lockTrace
        >> Trace.callEndpoint @"guess" w2 (GuessParams "SECRET")
        >> Trace.handleBlockchainEvents w2

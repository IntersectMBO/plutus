-- | A guessing game
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds       #-}
module Language.PlutusTx.Coordination.Contracts.Game(
    lock,
    guess,
    startGame,
    -- * Scripts
    gameValidator,
    gameDataScript,
    gameRedeemerScript,
    -- * Address
    gameAddress
    ) where

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Prelude    as P
import           Ledger
import           Ledger.Value                 (Value)
import           Wallet

import qualified Data.ByteString.Lazy.Char8   as C

data HashedString = HashedString P.ByteString

PlutusTx.makeLift ''HashedString

data ClearString = ClearString P.ByteString

PlutusTx.makeLift ''ClearString

correctGuess :: HashedString -> ClearString -> Bool
correctGuess (HashedString actual) (ClearString guess') =
    P.equalsByteString actual (P.sha2_256 guess')

validateGuess :: HashedString -> ClearString -> PendingTx -> ()
validateGuess dataScript redeemerScript _ =
    if correctGuess dataScript redeemerScript
    then ()
    else P.traceErrorH "WRONG!"

gameValidator :: ValidatorScript
gameValidator =
    ValidatorScript ($$(Ledger.compileScript [|| validateGuess ||]))

gameDataScript :: String -> DataScript
gameDataScript =
    DataScript . Ledger.lifted . HashedString . plcSHA2_256 . C.pack

gameRedeemerScript :: String -> RedeemerScript
gameRedeemerScript =
    RedeemerScript . Ledger.lifted . ClearString . C.pack

gameAddress :: Address
gameAddress = Ledger.scriptAddress gameValidator

lock :: (WalletAPI m, WalletDiagnostics m) => String -> Value -> m ()
lock word vl = do
    let ds = gameDataScript word
    payToScript_ defaultSlotRange gameAddress vl ds

guess :: (WalletAPI m, WalletDiagnostics m) => String -> m ()
guess word = do
    let redeemer = gameRedeemerScript word
    collectFromScript defaultSlotRange gameValidator redeemer

-- | Tell the wallet to start watching the address of the game script
startGame :: WalletAPI m => m ()
startGame = startWatching gameAddress

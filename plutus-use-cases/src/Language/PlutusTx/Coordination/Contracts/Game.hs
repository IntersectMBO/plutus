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
import qualified Ledger.Ada                   as Ada
import           Ledger.Ada                   (Ada)
import           Wallet

import qualified Data.ByteString.Lazy.Char8   as C

data HashedString = HashedString (P.SizedByteString 32)

PlutusTx.makeLift ''HashedString

data ClearString = ClearString (P.SizedByteString 32)

PlutusTx.makeLift ''ClearString

gameValidator :: ValidatorScript
gameValidator = ValidatorScript ($$(Ledger.compileScript [||
    \(HashedString actual) (ClearString guess') (_ :: PendingTx) ->

    if $$(P.equalsByteString) actual ($$(P.sha2_256) guess')
    then ()
    else $$(P.traceH) "WRONG!" ($$(P.error) ())

    ||]))

gameDataScript :: String -> DataScript
gameDataScript = 
    DataScript . Ledger.lifted . HashedString . plcSHA2_256 . P.SizedByteString . C.pack

gameRedeemerScript :: String -> RedeemerScript
gameRedeemerScript = 
    RedeemerScript . Ledger.lifted . ClearString . P.SizedByteString . C.pack

gameAddress :: Address
gameAddress = Ledger.scriptAddress gameValidator

lock :: (WalletAPI m, WalletDiagnostics m) => String -> Ada -> m ()
lock word adaVl = do
    let vl = Ada.toValue adaVl
        ds = gameDataScript word
    payToScript_ defaultSlotRange gameAddress vl ds

guess :: (WalletAPI m, WalletDiagnostics m) => String -> m ()
guess word = do
    let redeemer = gameRedeemerScript word
    collectFromScript defaultSlotRange gameValidator redeemer

-- | Tell the wallet to start watching the address of the game script
startGame :: WalletAPI m => m ()
startGame = startWatching gameAddress

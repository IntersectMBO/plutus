-- | A guessing game
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds       #-}
module Language.PlutusTx.Coordination.Contracts.Game(
    lock,
    guess,
    startGame
    ) where

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Prelude    as P
import           Ledger
import           Ledger.Validation
import qualified Ledger.Ada                   as Ada
import           Ledger.Ada                   (Ada)
import           Wallet

import           Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8   as C

data HashedString = HashedString ByteString

PlutusTx.makeLift ''HashedString

data ClearString = ClearString ByteString

PlutusTx.makeLift ''ClearString

gameValidator :: ValidatorScript
gameValidator = ValidatorScript ($$(Ledger.compileScript [||
    \(ClearString guess') (HashedString actual) (_ :: PendingTx) ->

    if $$(P.equalsByteString) actual ($$(P.sha2_256) guess')
    then ()
    else $$(P.traceH) "WRONG!" ($$(P.error) ())

    ||]))

gameAddress :: Address
gameAddress = Ledger.scriptAddress gameValidator

lock :: (WalletAPI m, WalletDiagnostics m) => String -> Ada -> m ()
lock word adaVl = do
    let hashedWord = plcSHA2_256 (C.pack word)
        vl = Ada.toValue adaVl
        ds = DataScript (Ledger.lifted (HashedString hashedWord))
    payToScript_ defaultSlotRange gameAddress vl ds

guess :: (WalletAPI m, WalletDiagnostics m) => String -> m ()
guess word = do
    let clearWord = C.pack word
        redeemer = RedeemerScript (Ledger.lifted (ClearString clearWord))
    collectFromScript defaultSlotRange gameValidator redeemer

-- | Tell the wallet to start watching the address of the game script
startGame :: WalletAPI m => m ()
startGame = startWatching gameAddress

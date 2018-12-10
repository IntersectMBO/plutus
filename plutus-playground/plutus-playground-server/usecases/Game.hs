module Language.PlutusTx.Coordination.Contracts.Game where

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Prelude    as P
import           Ledger
import           Ledger.Validation
import           Wallet
import           Playground.Contract

import qualified Data.ByteString.Lazy.Char8   as C

data HashedString = HashedString ByteString

PlutusTx.makeLift ''HashedString

-- create a data script for the guessing game by hashing the string
-- and lifting the hash to its on-chain representation
mkDataScript :: String -> DataScript
mkDataScript word = 
    let hashedWord = plcSHA2_256 (C.pack word)
    in  DataScript (Ledger.lifted (HashedString hashedWord))

data ClearString = ClearString ByteString

PlutusTx.makeLift ''ClearString

-- create a redeemer script for the guessing game by lifting the
-- string to its on-chain representation
mkRedeemerScript :: String -> RedeemerScript
mkRedeemerScript word = 
    let clearWord = C.pack word
    in RedeemerScript (Ledger.lifted (ClearString clearWord))

gameValidator :: ValidatorScript
gameValidator = ValidatorScript (Ledger.fromCompiledCode $$(PlutusTx.compile [||
    \(ClearString guess) (HashedString actual) (p :: PendingTx') ->

    if $$(P.equalsByteString) actual ($$(P.sha2_256) guess)
    then ()
    else $$(P.traceH) "WRONG!" ($$(P.error) ())

    ||]))

gameAddress :: Address'
gameAddress = Ledger.scriptAddress gameValidator

lock :: String -> Value -> MockWallet ()
lock word value = payToScript_ gameAddress value (mkDataScript word)

guess :: String -> MockWallet ()
guess word = collectFromScript gameValidator (mkRedeemerScript word)

-- | Tell the wallet to start watching the address of the game script
startGame :: MockWallet ()
startGame = startWatching gameAddress

$(mkFunction 'lock)
$(mkFunction 'guess)
$(mkFunction 'startGame)

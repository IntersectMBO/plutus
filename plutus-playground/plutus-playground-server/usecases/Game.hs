module Language.PlutusTx.Coordination.Contracts.Game where

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Prelude    as P
import           Ledger
import           Ledger.Validation
import           Wallet
import           Playground.Contract

import qualified Data.ByteString.Char8        as C

data HashedString = HashedString ByteString
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''HashedString

data ClearString = ClearString ByteString
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''ClearString

gameValidator :: ValidatorScript
gameValidator = ValidatorScript (Ledger.fromPlcCode $$(PlutusTx.plutus [||
    \(ClearString guess) (HashedString actual) (p :: PendingTx ValidatorHash) ->

    if $$(P.equalsByteString) actual ($$(P.sha2_256) guess)
    then ()
    else $$(P.traceH) "WRONG!" ($$(P.error) ())

    ||]))

gameAddress :: Address'
gameAddress = Ledger.scriptAddress gameValidator

lock :: String -> Value -> MockWallet ()
lock word value = do
    let hashedWord = plcSHA2_256 (C.pack word)
        ds = DataScript (Ledger.lifted (HashedString hashedWord))
    _ <- payToScript gameAddress value ds
    pure ()

guess :: String -> MockWallet ()
guess word = do
    let clearWord = C.pack word
        redeemer = RedeemerScript (Ledger.lifted clearWord)
    collectFromScript gameValidator redeemer

-- | Tell the wallet to start watching the address of the game script
startGame :: MockWallet ()
startGame = startWatching gameAddress

$(mkFunction 'lock)
$(mkFunction 'guess)
$(mkFunction 'startGame)

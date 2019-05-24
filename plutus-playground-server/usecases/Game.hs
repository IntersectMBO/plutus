{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
module Game where
-- TRIM TO HERE
-- A game with two players. Player 1 thinks of a secret word
-- and uses its hash, and the game validator script, to lock
-- some funds (the prize) in a pay-to-script transaction output.
-- Player 2 guesses the word by attempting to spend the transaction
-- output. If the guess is correct, the validator script releases the funds.
-- If it isn't, the funds stay locked.
import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Prelude    as P
import           Ledger
import qualified Ledger.Value                 as Value
import           Ledger.Value                 (Value)
import           Ledger.Validation
import           Wallet
import           Playground.Contract

import qualified Data.ByteString.Lazy.Char8   as C

data HashedString = HashedString P.ByteString

PlutusTx.makeLift ''HashedString

data ClearString = ClearString P.ByteString

PlutusTx.makeLift ''ClearString

correctGuess :: HashedString -> ClearString -> Bool
correctGuess (HashedString actual) (ClearString guess') =
    P.equalsByteString actual (P.sha2_256 guess')

validateGuess :: HashedString -> ClearString -> PendingTx -> Bool
validateGuess dataScript redeemerScript _ = correctGuess dataScript redeemerScript

-- | The validator script of the game.
gameValidator :: ValidatorScript
gameValidator =
    ValidatorScript ($$(Ledger.compileScript [|| validateGuess ||]))

-- create a data script for the guessing game by hashing the string
-- and lifting the hash to its on-chain representation
gameDataScript :: String -> DataScript
gameDataScript =
    DataScript . Ledger.lifted . HashedString . plcSHA2_256 . C.pack

-- create a redeemer script for the guessing game by lifting the
-- string to its on-chain representation
gameRedeemerScript :: String -> RedeemerScript
gameRedeemerScript =
    RedeemerScript . Ledger.lifted . ClearString . C.pack

-- | The address of the game (the hash of its validator script)
gameAddress :: Address
gameAddress = Ledger.scriptAddress gameValidator

-- | The "lock" contract endpoint. See note [Contract endpoints]
lock :: MonadWallet m => String -> Value -> m ()
lock word vl =
    -- 'payToScript_' is a function of the wallet API. It takes a script
    -- address, a currency value and a data script, and submits a transaction
    -- that pays the value to the address, using the data script.
    --
    -- The underscore at the end of the name indicates that 'payToScript_'
    -- discards its result. If you want to hold on to the transaction you can
    -- use 'payToScript'.
    payToScript_ defaultSlotRange gameAddress vl (gameDataScript word)

-- | The "guess" contract endpoint. See note [Contract endpoints]
guess :: (WalletAPI m, WalletDiagnostics m) => String -> m ()
guess word = do
    let redeemer = gameRedeemerScript word
    -- 'collectFromScript' is a function of the wallet API. It consumes the
    -- unspent transaction outputs at a script address and pays them to a
    -- public key address owned by this wallet. It takes the validator script
    -- and the redeemer scripts as arguments.
    --
    -- Note that before we can use 'collectFromScript', we need to tell the
    -- wallet to start watching the address for transaction outputs (because
    -- the wallet does not keep track of the UTXO set of the entire chain).
    collectFromScript defaultSlotRange gameValidator redeemer

-- | The "startGame" contract endpoint, telling the wallet to start watching
--   the address of the game script. See note [Contract endpoints]
startGame :: MonadWallet m => m ()
startGame =
    -- 'startWatching' is a function of the wallet API. It instructs the wallet
    -- to keep track of all outputs at the address. Player 2 needs to call
    -- 'startGame' before Player 1 uses the 'lock' endpoint, to ensure that
    -- Player 2's wallet is aware of the game address.
    startWatching gameAddress

$(mkFunctions ['lock, 'guess, 'startGame])

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

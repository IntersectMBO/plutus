-- | A game with two players. Player 1 thinks of a secret word
--   and uses its hash, and the game validator script, to lock
--   some funds (the prize) in a pay-to-script transaction output.
--   Player 2 guesses the word by attempting to spend the transaction
--   output. If the guess is correct, the validator script releases the funds.
--   If it isn't, the funds stay locked.
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

-- | The validator script of the game.
gameValidator :: ValidatorScript
gameValidator = ValidatorScript ($$(Ledger.compileScript [||
    -- The code between the '[||' and  '||]' quotes is on-chain code.
    \(ClearString guess) (HashedString actual) (p :: PendingTx) ->

    -- inside the on-chain code we can write $$(P.xxx) to use functions
    -- from the PlutusTx Prelude (imported qualified at the top of the
    -- module)
    if $$(P.equalsByteString) actual ($$(P.sha2_256) guess)
    then ()
    else ($$(P.error) ($$(P.traceH) "WRONG!" ()))

    ||]))

-- | The address of the game (the hash of its validator script)
gameAddress :: Address
gameAddress = Ledger.scriptAddress gameValidator

-- | The "lock" contract endpoint. See note [Contract endpoints]
lock :: String -> Value -> MockWallet ()
lock word value =
    -- 'payToScript_' is a function of the wallet API. It takes a script
    -- address, a value and a data script, and submits a transaction that
    -- pays the value to the address, using the data script.
    --
    -- The underscore at the end of the name indicates that 'payToScript_'
    -- discards its result. If you want to hold on to the transaction you can
    -- use 'payToScript'.
    payToScript_ defaultSlotRange gameAddress value (mkDataScript word)

-- | The "guess" contract endpoint. See note [Contract endpoints]
guess :: String -> MockWallet ()
guess word =
    -- 'collectFromScript' is a function of the wallet API. It consumes the
    -- unspent transaction outputs at a script address and pays them to a
    -- public key address owned by this wallet. It takes the validator script
    -- and the redeemer scripts as arguments.
    --
    -- Note that before we can use 'collectFromScript', we need to tell the
    -- wallet to start watching the address for transaction outputs (because
    -- the wallet does not keep track of the UTXO set of the entire chain).
    collectFromScript defaultSlotRange gameValidator (mkRedeemerScript word)

-- | The "startGame" contract endpoint, telling the wallet to start watching
--   the address of the game script. See note [Contract endpoints]
startGame :: MockWallet ()
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

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-
    A Plutus emulator (mockchain) tutorial. This is the fourth in a series of
    tutorials:

    1. [Plutus Tx](../../doctest/Tutorial/01-plutus-tx.md)
    2. [A guessing game](../../doctest/Tutorial/02-validator-scripts.md)
    3. [A crowdfunding campaign](../../doctest/Tutorial/03-plutus-wallet-api.md)
    4. Working with the emulator (this tutorial)
    5. [A multi-stage contract](./Vesting.hs)

-}
module Tutorial.Emulator where

import qualified Data.Map                     as Map

import qualified Language.PlutusTx            as P
import           Ledger                       (Address, DataScript(..), RedeemerScript(..), ValidatorScript(..), Value)
import qualified Ledger                       as L
import           Ledger.Validation            (PendingTx)
import qualified Ledger.Ada                   as Ada
import           Ledger.Ada                   (Ada)
import           Wallet                       (WalletAPI(..), WalletDiagnostics(..))
import qualified Wallet                       as W
import qualified Wallet.Generators            as Gen
import qualified Wallet.Emulator.Types        as EM
import qualified Wallet.API                   as WAPI

import qualified Tutorial.Solutions1          as TH
import qualified Tutorial.ExUtil              as EXU

-- | $setup
-- >>> import Tutorial.Emulator
-- >>> import qualified Wallet.Emulator.Types as EM

{- |
    Compiling Plutus programs

    To use `TH.trickier` from `Tutorial.TH` in our smart contract we need to
    compile it using `Language.PlutusTx.compile :: Q (TExp a) -> CompiledCode
    a`. `compile` takes a typed Template Haskell quote and compiles it to
    Plutus Core. The parameter `a` indicates that the generated program is of
    the Plutus type that corresponds to `a`.

    We need some instances of `trickier` with different parameters:

-}

trickier2 :: P.CompiledCode (Integer -> Integer)
trickier2 = $$(P.compile [|| $$(TH.trickier 2) ||])

trickier5 :: P.CompiledCode (Integer -> Integer)
trickier5 = $$(P.compile [|| $$(TH.trickier 5) ||])

trickier10 :: P.CompiledCode (Integer -> Integer)
trickier10 = $$(P.compile [|| $$(TH.trickier 10) ||])

{- |

    `Language.PlutusTx.Plugin.sizePlc` tells us the size in bytes of a piece of
    `CompiledCode` when placed in a transaction.

    E3. Use `sizePlc` to get the size of `trickier2` and `trickier5`. How large
    do you expect `trickier10` to be?

    E3* Write a function `trickier10Light` that computes the same
        result as `trickier10`, but has a smaller code size when compiled to Plutus.

-}

{- |
    Part 3. Testing smart contracts in GHCi, using the mockchain

    E4: Below is the outline of a contract similar to the guessing game. It
        uses `trickier2` instead of `hash`. Fill in the missing
        definitions in `intGameValidator` and the `lock` and `guess` endpoints.

-}

data SecretNumber = SecretNumber Integer
P.makeLift ''SecretNumber

data ClearNumber = ClearNumber Integer
P.makeLift ''ClearNumber

intGameValidator :: ValidatorScript
intGameValidator = error "exercise"

gameAddress :: Address
gameAddress = L.scriptAddress intGameValidator

lock :: (WalletAPI m, WalletDiagnostics m) => Integer -> Ada -> m ()
lock _i adaVl = do
    let secretInt = error "exercise"
        vl = Ada.toValue adaVl
        ds = DataScript (L.lifted (SecretNumber secretInt))
    W.payToScript_ W.defaultSlotRange gameAddress vl ds

guess :: (WalletAPI m, WalletDiagnostics m) => Integer -> m ()
guess i = do
    let redeemer = RedeemerScript (L.lifted (ClearNumber i))
    W.collectFromScript W.defaultSlotRange intGameValidator redeemer

-- | Tell the wallet to start watching the address of the game script
startGame :: WalletAPI m => m ()
startGame = startWatching gameAddress

{- |

    We now have a new contract with three endpoints, 'lock', 'guess' and
    'startGame', very much like the existing guessing game.

    Instead of using the Playground to test this contract we are going to work
    with the mockchain directly, in GHCi.

    The mockchain is a simplified model of the cardano blockchain. Its internal
    state consists of two parts: A _global_ part containing the blockchain
    (list of validated blocks) and a transaction pool (transactions that have
    been submitted but have not been validated yet). And a _local_,
    wallet-specific part with information about how much of the blockchain is
    known to each wallet and about the amount of "own" funds. A wallet's own
    funds are unspent pay-to-pubkey transaction outputs that can be spent by
    the wallet.

    Let's run through an example. Suppose wallet 'w1' wants to transfer 100 Ada
    to wallet 'w2' using a transaction 't'.

    The life cycle of 't' in the emulator looks like this:

    1. 'w1' constructs 't' using the wallet API by calling
       'Wallet.API.payToPublicKey', and submits 't' to the transaction pool.
    2. The emulator validates 't', along with any other pending transactions
       from the transaction pool, and adds a new block containing 't' to the
       blockchain.
    3. 'w1' and 'w2' are notified of the new block and update their internal
       state accordingly: The "own funds" of 'w1' decrease by 100 Ada and the
       "own funds" of 'w2' increase by the same amount.

    When working with the mockchain we use the `Trace` type to build a sequence
    of actions similar to steps (1) through (3) above. To implement the example
    in Haskell we need two wallets 'w1' and 'w2'.

-}

-- Some wallets used for testing.
w1, w2 :: EM.Wallet
w1 = EM.Wallet 1
w2 = EM.Wallet 2

-- To send money to a wallet we need to know its public key.
pk1, pk2 :: WAPI.PubKey
pk1 = EM.walletPubKey w1
pk2 = EM.walletPubKey w2

{- |

    Now we can build a trace that performs the three steps. A `Trace m a` is a
    sequence of mockchain operations, where `m` is the type in which wallet
    actions take place (usually `m` is an instance of `WalletAPI`) and
    `a` is the return type.

    The 'Wallet.Emulator.Types' module provides all the functions we need for
    building traces.

-}

simpleTrace :: (Monad m, WalletAPI m) => EM.Trace m ()
simpleTrace = do
    -- 1. Wallet 'w1' constructs the transaction 't'.
    _ <- EM.walletAction w1

            -- The second argument to 'walletAction' is an action in
            -- 'WalletAPI'. We call 'payToPublicKey_' here but we could
            -- also call any number of our own contract endpoints.
            $ W.payToPublicKey_

                -- The transaction can be validated at any time
                WAPI.defaultSlotRange

                -- We want to transfer 100 Ada
                (Ada.adaValueOf 100)

                -- The recipient's public key is 'pk2'
                pk2

    -- 2. The emulator validates all pending transactions. `EM.processPending`
    --    returns the newly added block.
    blck <- EM.processPending

    -- 3. Notify all wallets of the new block.
    _ <- EM.walletsNotifyBlock [w1, w2] blck

    -- Done!
    pure ()


{-
    Note that the last two steps (process pending transactions and notify
    wallets of the new block) can be combined using the function
    `EM.addBlocksAndNotify`.

    How can we run a `Trace`? The module `Wallet.Emulator.Types` exports the
    function `runTraceTxPool :: TxPool -> Trace MockWallet a -> (Either
    AssertionError a, EmulatorState)`. `runTraceTxPool` runs a complete trace
    on a blockchain that is initially empty. Its arguments are the list of
    pending transactions at the beginning of the simulation -- that is,
    transactions that have been submitted to the chain but not confirmed yet --
    and the trace itself. The `TxPool` argument can be used to supply an
    initial transaction that forges the money we work with and distributes it to
    the wallets.

    `Ledger.ExUtil` contains such an initial transaction, called
    `initialTx`. It assigns 1000 Ada each to wallet 1 and wallet 2.

    >>> Ledger.ExUtil.initialTx
    Tx {txInputs = fromList [], txOutputs = [TxOutOf {txOutAddress = AddressOf {getAddress = 9c12cfdc04c74584d787ac3d23772132c18524bc7ab28dec4219b8fc5b425f70}, txOutValue = Value {getValue = [(CurrencySymbol 0,1000)]}, txOutType = PayToPubKey (PubKey {getPubKey = 1})},TxOutOf {txOutAddress = AddressOf {getAddress = 1cc3adea40ebfd94433ac004777d68150cce9db4c771bc7de1b297a7b795bbba}, txOutValue = Value {getValue = [(CurrencySymbol 0,1000)]}, txOutType = PayToPubKey (PubKey {getPubKey = 2})}], txForge = Value {getValue = [(CurrencySymbol 0,2000)]}, txFee = Ada {getAda = 0}, txValidRange = Interval {ivFrom = Nothing, ivTo = Nothing}}

    When the simulation starts, `initialTx` needs to be validated and added to
    the blockchain (as the first block).

    Let's define an alias that lets us run traces easily.
-}

-- | A helper function for running traces. 'runTrace''
--   * Forges some funds using the initial transaction from Ledger.ExUtils, to
--     ensure that the wallets have enough funds
--
--   * Instantiates the trace's type parameter 'm' with 'MockWallet', the
--     mockchain's wallet API
runTrace' :: EM.Trace EM.MockWallet a -> (Either EM.AssertionError a, EM.EmulatorState)
runTrace' trc = EM.runTraceTxPool [EXU.initialTx] $ do

    -- before we run the argument trace 'trc' we need to validate the initial
    -- transaction and notify all wallets. If we don't do that, then the wallets
    -- will assume that they don't own any unspent transaction outputs, and all
    -- attempts to make non-zero payments will fail.
    _ <- EM.addBlocksAndNotify [w1, w2] 1

    -- now we can run 'trc'.
    trc


{- |
    >>> runTrace' simpleTrace
    ...

    The result of `runTrace'` as displayed by GHCi is not very meaningful
    because it contains too much information: It includes the entire blockchain,
    the internal states of all wallets, pending transactions, log events, and
    so on. To only see the final distribution of funds to wallets, use `EM.fundsDistribution :: EmulatorState -> Map Wallet Value`:

-}

simpleTraceDist :: Map.Map EM.Wallet Value
simpleTraceDist = EM.fundsDistribution $ snd $ runTrace' simpleTrace
{- |

    >>> simpleTraceDist
    fromList [(Wallet {getWallet = 1},Value {getValue = Map {unMap = [(,Map {unMap = [(,900)]})]}}),(Wallet {getWallet = 2},Value {getValue = Map {unMap = [(,Map {unMap = [(,1100)]})]}})]

    'simpleTraceDist' shows that our transaction was successful: Wallet 1 now
    owns 900 Ada (the currency identified by )

-}

{- A complete trace for the new int guessing game looks like this:
-}

gameSuccess :: (WalletAPI m, WalletDiagnostics m) => EM.Trace m ()
gameSuccess = do

    -- The secret
    let secretNumber = 5

    -- 1. Wallet 'w1' starts watching the game address using the 'startGame'
    --    endpoint
    _ <- EM.walletAction w1 startGame

    -- 2. Wallet 'w2' locks some funds
    _ <- EM.walletAction w2 (lock secretNumber (Ada.fromInt 500))

    -- 3. Process this transaction and notify all wallets
    _ <- EM.addBlocksAndNotify [w1, w2] 1

    -- 4. 'w1' makes a guess
    _ <- EM.walletAction w1 (guess secretNumber)

    -- 5. Process this transaction and notify all wallets
    _ <- EM.addBlocksAndNotify [w1, w2] 1

    -- Done.
    pure ()

{- |
    The final distribution after 'gameSuccess' looks as we would expect:

    >>> EM.fundsDistribution $ snd $ runTrace' simpleTrace
    fromList [(Wallet {getWallet = 1},Value {getValue = Map {unMap = [(,Map {unMap = [(,900)]})]}}),(Wallet {getWallet = 2},Value {getValue = Map {unMap = [(,Map {unMap = [(,1100)]})]}})]

-}

gameFailure :: (WalletAPI m, WalletDiagnostics m) => EM.Trace m ()
gameFailure = do

    -- The secret
    let secretNumber = 5

    -- 1. Wallet 'w1' starts watching the game address using the 'startGame'
    --    endpoint
    _ <- EM.walletAction w1 startGame

    -- 2. Wallet 'w2' locks some funds
    _ <- EM.walletAction w2 (lock secretNumber (Ada.fromInt 500))

    -- 3. Process this transaction and notify all wallets
    _ <- EM.addBlocksAndNotify [w1, w2] 1

    -- 4. 'w1' makes a guess
    _ <- EM.walletAction w1 (guess 4)

    -- 5. Process this transaction and notify all wallets
    _ <- EM.addBlocksAndNotify [w1, w2] 1

    -- Done.
    pure ()

{-

    Sometimes a trace does not give the result we were expecting. In this
    case we can inspect the emulator log to see where it went wrong. The
    emulator log contains a list of blockchain events, telling us when a block
    was added and when transactions were submitted to the pool and validated.

    >>> emLog $ snd $ runTrace' gameFailure
    [SlotAdd (Slot {getSlot = 3}),TxnValidationFail (TxIdOf {getTxId = d6757dbb663d0f560d553972bc44e60384dc6e5d3c12295114d30b77d27a2856}) (ScriptFailure ["Wrong number"]),TxnSubmit (TxIdOf {getTxId = d6757dbb663d0f560d553972bc44e60384dc6e5d3c12295114d30b77d27a2856}),SlotAdd (Slot {getSlot = 2}),TxnValidate (TxIdOf {getTxId = 566c02f59e744ca0fc1d2eeb424524f133e9de21331b00e655beb28a76d932b0}),TxnSubmit (TxIdOf {getTxId = 566c02f59e744ca0fc1d2eeb424524f133e9de21331b00e655beb28a76d932b0}),SlotAdd (Slot {getSlot = 1}),TxnValidate (TxIdOf {getTxId = bd9fa121a44d5b39f3ae4a259cc97866bbb8aa640156afb6ac29d3e5b3eddfd0})]

    The log entries appear in reverse chronological order (newest first). The
    second entry of the log above shows that a transaction failed with the
    message "Wrong number".

    E5. Implement the int game in the Playground and run the 'gameSuccess' and
       'gameFailure' traces in the Playground. Compare the final distribution
       and emulator logs.
       NOTE. In the Playground, every contract has to be written in a single
       file. Therefore we can't define the TH quoted function 'trickier' in a separate module, so you have to write it directly in the validator script (in place of $$(TH.trickier 2)). (See also exercise E3*)

-}

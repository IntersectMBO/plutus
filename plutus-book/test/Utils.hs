module Utils
    ( w1
    , w2
    , w3
    , key1
    , key2
    , key3
    , initialAda
    , getResult
    , updateWallets
    , assertFunds2
    , assertFunds3
    ) where

import           Ledger
import           Ledger.Ada
import           Wallet.Emulator
import           Wallet.Emulator.Generators
import           Wallet.Generators

import           Control.Arrow              (first)
import           Control.Monad              (void)
import qualified Data.Map.Strict            as Map

w1, w2, w3 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3

key1, key2, key3 :: PubKey
key1 = walletPubKey w1
key2 = walletPubKey w2
key3 = walletPubKey w3

initialAda :: Ada
initialAda = fromInt 100000

initialChain :: Mockchain
initialChain =
    let (txn, ot) = genInitialTransaction generatorModel
        txId      = hashTx txn
    in  Mockchain {
            mockchainInitialBlock = [txn],
            mockchainUtxo = Map.fromList $ first (TxOutRefOf txId) <$> zip [0..] ot
        }

updateWallets :: Trace MockWallet ()
updateWallets = void $ processPending >>= walletsNotifyBlock [w1, w2, w3]

getResult :: Trace MockWallet () -> (Either AssertionError (), EmulatorState)
getResult = runTrace initialChain

assertFunds2 :: Ada -> Ada -> Trace MockWallet ()
assertFunds2 ada1 ada2 = do
    assertOwnFundsEq w1 $ toValue ada1
    assertOwnFundsEq w2 $ toValue ada2

assertFunds3 :: Ada -> Ada -> Ada -> Trace MockWallet ()
assertFunds3 ada1 ada2 ada3 = do
    assertOwnFundsEq w1 $ toValue ada1
    assertOwnFundsEq w2 $ toValue ada2
    assertOwnFundsEq w3 $ toValue ada3

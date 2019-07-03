module Utils
    ( w1
    , w2
    , w3
    , initialAda
    , getResult
    , updateWallets
    , assertFunds
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
w3 = Wallet 2

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

assertFunds :: Ada -> Ada -> Trace MockWallet ()
assertFunds ada1 ada2 = do
    assertOwnFundsEq w1 $ toValue ada1
    assertOwnFundsEq w2 $ toValue ada2

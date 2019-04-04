{-# LANGUAGE FlexibleContexts #-}
module Spec.MultiSig(tests) where

import           Control.Lens
import           Control.Monad                                     (void)
import           Control.Monad.Except
import           Data.Either                                       (isLeft, isRight)
import qualified Data.Map                                          as Map
import qualified Data.Text                                         as T

import           Test.Tasty
import qualified Test.Tasty.HUnit                                  as HUnit

import           Language.PlutusTx.Coordination.Contracts.MultiSig as MS
import           Ledger                                            (PrivateKey, Tx, hashTx, signatures, toPublicKey)
import qualified Ledger.Ada                                        as Ada
import qualified Ledger.Crypto                                     as Crypto
import qualified Wallet.API                                        as WAPI
import qualified Wallet.Emulator                                   as EM

tests :: TestTree
tests = testGroup "multisig" [
    HUnit.testCase "three out of five" (nOutOfFiveTest 3),
    HUnit.testCase "two out of five" (nOutOfFiveTest 2)
    ]

nOutOfFiveTest :: Int -> HUnit.Assertion
nOutOfFiveTest i = do
    let initialState = EM.emulatorStateInitialDist (Map.singleton (EM.walletPubKey (EM.Wallet 1)) (Ada.adaValueOf 10))
        (result, _) = EM.runEmulator initialState (threeOutOfFive i)
        isOk = if i < 3 then isLeft result else isRight result
    HUnit.assertBool "transaction failed to validate" isOk

-- | A mockchain trace that locks funds in a three-out-of-five multisig
--   contract, and attempts to spend them using the given number of signatures.
--   @threeOutOfFive 3@ passes, @threeOutOfFive 2@ results in an
--   'EM.AssertionError'.
threeOutOfFive :: (EM.MonadEmulator m) => Int -> m ()
threeOutOfFive n = do

    let
        w1 = EM.Wallet 1
        w2 = EM.Wallet 2

        -- a 'MultiSig' contract that requires three out of five signatures
        ms = MultiSig
                { signatories = EM.walletPubKey . EM.Wallet <$> [1..5]
                , requiredSignatures = 3
                }

        processAndNotify = void (EM.addBlocksAndNotify [w1, w2] 1)

    -- the first trace produces the transaction that needs to be signed
    (r, _) <- EM.processEmulated $ do
            processAndNotify
            void $ EM.walletAction w2 (initialise ms)
            processAndNotify
            void $ EM.walletAction w1 (lock ms $ Ada.adaValueOf 10)
            processAndNotify
            EM.runWalletAction w2 (unlockTx ms)

    tx <- either (throwError . EM.AssertionError . T.pack . show) pure r

    let
        -- Attach signatures of the first @n@ wallets' private keys to 'tx'.
        signedTx =
            let signingKeys = take n (EM.walletPrivKey . EM.Wallet <$> [1..]) in
            foldr attachSignature tx signingKeys

    -- the second trace submits the signed transaction and asserts
    -- that it has been validated.
    EM.processEmulated $ do
        void $ EM.walletAction w2 (WAPI.submitTxn signedTx)
        processAndNotify
        EM.assertIsValidated signedTx

-- | Attach a signature to a transaction.
attachSignature :: PrivateKey -> Tx -> Tx
attachSignature pk tx' =
    let sig = Crypto.signTx (hashTx tx') pk
    in  tx' & signatures . at (toPublicKey pk) ?~ sig

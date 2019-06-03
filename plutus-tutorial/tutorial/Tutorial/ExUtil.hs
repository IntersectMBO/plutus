{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- Some utility functions for the tutorials
module Tutorial.ExUtil(
      encode
    , initialTx
    , w1
    , w2
    , w3
    , pk1
    , pk2
    , pk3
    , runTrace
    , runTraceDist
    , runTraceLog
    ) where

import qualified Data.Map                  as Map
import qualified Data.Set                  as S
import qualified Language.PlutusTx.Prelude as P
import           Ledger
import qualified Ledger.Ada                as Ada
import qualified Ledger.Value              as Value
import qualified Wallet.API                as WAPI
import qualified Wallet.Emulator.Types     as EM
import qualified Wallet.Generators         as Gen

{-# INLINABLE encode #-}
encode :: Integer -> Integer
encode x = x `P.multiply` 2

initialTx :: Tx
initialTx =
    let oneThousand = Ada.adaValueOf 1000
    in Tx
        { txInputs = S.empty
        , txOutputs =
            [ pubKeyTxOut oneThousand pk1
            , pubKeyTxOut oneThousand pk2
            , pubKeyTxOut oneThousand pk3
            ]
        , txForge = oneThousand `Value.plus` oneThousand `Value.plus` oneThousand
        , txFee = Ada.zero
        , txValidRange = WAPI.defaultSlotRange
        , txSignatures = Map.empty
        }

-- Some wallets used for testing. The 'Wallet.Generators' module defines a
-- number of wallets for this purpose.
w1, w2, w3 :: EM.Wallet
w1 = EM.Wallet 1
w2 = EM.Wallet 2
w3 = EM.Wallet 3

-- To send money to a wallet we need to know its public key.
pk1, pk2, pk3 :: WAPI.PubKey
pk1 = EM.walletPubKey w1
pk2 = EM.walletPubKey w2
pk3 = EM.walletPubKey w3

-- | A helper function for running traces. 'runTrace'
--   * Forges some funds using the initial transaction from Ledger.ExUtils, to
--     ensure that the wallets have enough funds
--
--   * Instantiates the trace's type parameter 'm' with 'MockWallet', the
--     mockchain's wallet API
runTrace :: EM.Trace EM.MockWallet a -> (Either EM.AssertionError a, EM.EmulatorState)
runTrace trc = EM.runTraceTxPool [initialTx] $ do

    -- before we run the argument trace 'trc' we need to validate the initial
    -- transaction and notify all wallets. If we don't do that, then the wallets
    -- will assume that they don't own any unspent transaction outputs, and all
    -- attempts to make non-zero payments will fail.
    _ <- EM.addBlocksAndNotify [w1, w2, w3] 1

    -- now we can run 'trc'.
    trc

runTraceDist :: EM.Trace EM.MockWallet a -> Map.Map EM.Wallet Value.Value
runTraceDist = EM.fundsDistribution . snd . runTrace

runTraceLog :: EM.Trace EM.MockWallet a -> [EM.EmulatorEvent]
runTraceLog = EM.emLog . snd . runTrace

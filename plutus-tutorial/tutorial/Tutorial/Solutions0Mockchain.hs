-- | Mockchain traces for the crowdfunding contract defined
--   in'Tutorial.Solutions0'
module Tutorial.Solutions0Mockchain where

import           Data.Foldable         (traverse_)
import qualified Language.PlutusTx     as P
import           Ledger                (Address, DataScript (..), PubKey (..), RedeemerScript (..), Signature (..),
                                        Slot (..), TxId, ValidatorScript (..))
import qualified Ledger                as L
import           Ledger.Ada            (Ada)
import qualified Ledger.Ada            as Ada
import qualified Ledger.Interval       as P
import qualified Ledger.Interval       as Interval
import           Ledger.Validation     (PendingTx (..), PendingTxIn (..), PendingTxOut)
import qualified Ledger.Validation     as V
import           Wallet                (EventHandler (..), EventTrigger, MonadWallet, WalletAPI (..),
                                        WalletDiagnostics (..))
import qualified Wallet                as W

import           Tutorial.Solutions0

import qualified Tutorial.ExUtil       as ExUtil
import qualified Wallet.Emulator.Types as EM

-- | A campaign for the traces
campaign :: Campaign
campaign =
  Campaign
      [(20, 100), (30, 200)]
      35
      ExUtil.pk1

--
-- The traces defined below this line can be run in GHCi
-- using the Tutorial.ExUtil module. They are of no use
-- in the Playground.
--
campaignSuccess :: MonadWallet m => EM.Trace m ()
campaignSuccess = do

    -- 1. Wallet 'w1' starts watching the contract address using the
    --    'registerVestingScheme' endpoint.
    _ <- EM.walletAction ExUtil.w1 (scheduleCollection campaign)

    -- 2. Wallet 'w2' contributes 80 Ada
    _ <- EM.walletAction ExUtil.w2 (contribute campaign 80)


    -- 2. Wallet 'w3' contributes 50 Ada
    _ <- EM.walletAction ExUtil.w3 (contribute campaign 50)

    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 25

    pure ()

campaignSuccess2 :: MonadWallet m => EM.Trace m ()
campaignSuccess2 = do

    -- 1. Wallet 'w1' starts watching the contract address using the
    --    'registerVestingScheme' endpoint.
    _ <- EM.walletAction ExUtil.w1 (scheduleCollection campaign)

    -- 2. Wallet 'w2' contributes 80 Ada
    _ <- EM.walletAction ExUtil.w2 (contribute campaign 80)

    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 25

    -- 2. Wallet 'w3' contributes 50 Ada
    _ <- EM.walletAction ExUtil.w3 (contribute campaign 150)

    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 5

    pure ()

campaignFail :: MonadWallet m => EM.Trace m ()
campaignFail = do

    -- 1. Wallet 'w1' starts watching the contract address using the
    --    'registerVestingScheme' endpoint.
    _ <- EM.walletAction ExUtil.w1 (scheduleCollection campaign)

    -- 2. Wallet 'w2' contributes 80 Ada
    _ <- EM.walletAction ExUtil.w2 (contribute campaign 80)

    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 20

    -- 2. Wallet 'w3' contributes 50 Ada
    _ <- EM.walletAction ExUtil.w3 (contribute campaign 50)

    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 20

    pure ()

-- | Mockchain traces for the crowdfunding contract defined
--   in'Tutorial.Solutions0'
module Tutorial.Solutions0Mockchain where

import           Data.Foldable         (traverse_)
import qualified Language.PlutusTx     as P
import           Ledger                (Address, DataScript (..), PubKey (..), RedeemerScript (..), Signature (..),
                                        Slot (..), TxId, ValidatorScript (..))
import qualified Ledger                as L
import           Ledger.Ada.TH         (Ada)
import qualified Ledger.Ada.TH         as Ada
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

--
-- The traces defined below this line can be run in GHCi
-- using the Tutorial.ExUtil module. They are of no use
-- in the Playground.
--
campaignSuccess :: MonadWallet m => EM.Trace m ()
campaignSuccess = do

    -- 1. Wallet 'w1' starts watching the contract address using the
    --    'scheduleCollection' endpoint.
    _ <- EM.walletAction ExUtil.w1 scheduleCollection

    -- 2. Wallet 'w2' contributes 80 Ada
    _ <- EM.walletAction ExUtil.w2 (contribute 80)


    -- 2. Wallet 'w3' contributes 50 Ada. This brings the total contributed
    --    to 130 Ada before Slot 10, so the campaign has been a success.
    _ <- EM.walletAction ExUtil.w3 (contribute 50)

    -- 3. Add a number of empty blocks. This causes wallet 1 to collect the
    --    two contributions.
    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 25

    pure ()

campaignSuccess2 :: MonadWallet m => EM.Trace m ()
campaignSuccess2 = do

    -- 1. Wallet 'w1' starts watching the contract address using the
    --    'scheduleCollection' endpoint.
    _ <- EM.walletAction ExUtil.w1 scheduleCollection

    -- 2. Wallet 'w2' contributes 80 Ada
    _ <- EM.walletAction ExUtil.w2 (contribute 80)

    -- 3. Advance the clock to slot 16. The first goal (100 Ada by slot 10)
    --    has been missed but the second goal (200 Ada by slot 20) is still
    --    possible.
    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 15

    -- 4. Wallet 'w3' contributes 150 Ada, taking the total to 230.
    _ <- EM.walletAction ExUtil.w3 (contribute 150)

    -- 5. Add some empty blocks, prompting wallet 1 to collect the funds.
    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 5

    pure ()

campaignFail :: MonadWallet m => EM.Trace m ()
campaignFail = do

    -- 1. Wallet 'w1' starts watching the contract address using the
    --    'scheduleCollection' endpoint.
    _ <- EM.walletAction ExUtil.w1 scheduleCollection

    -- 2. Wallet 'w2' contributes 80 Ada
    _ <- EM.walletAction ExUtil.w2 (contribute 80)

    -- 3. Advance the clock to slot 21. The campaign has failed.
    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 20

    -- 4. Wallet 'w3' contributes 50 Ada (too late!)
    _ <- EM.walletAction ExUtil.w3 (contribute 50)

    -- 5. Advance the clock past slot 25, causing w2 and w3 to collect
    --    their refunds.
    _ <- EM.addBlocksAndNotify [ExUtil.w1, ExUtil.w2, ExUtil.w3] 20

    pure ()


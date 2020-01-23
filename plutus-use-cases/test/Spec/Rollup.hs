{-# LANGUAGE FlexibleContexts #-}
module Spec.Rollup where


import           Data.ByteString.Lazy                                  (ByteString)
import qualified Data.ByteString.Lazy                                  as LBS
import qualified Data.Map                                              as Map
import qualified Data.Text                                             as T
import           Data.Text.Encoding                                    (encodeUtf8)

import           Ledger (pubKeyHash)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Trace

import           Language.Plutus.Contract.Request                      (ContractRow)
import           Language.PlutusTx.Coordination.Contracts.Crowdfunding
import           Language.PlutusTx.Coordination.Contracts.Game
import           Language.PlutusTx.Coordination.Contracts.Vesting
import qualified Spec.Vesting

import           Test.Tasty                                            (TestTree, testGroup)
import           Test.Tasty.Golden                                     (goldenVsString)
import           Test.Tasty.HUnit                                      (assertFailure)
import qualified Wallet.Emulator.Chain                                 as EM
import           Wallet.Emulator.Types
import qualified Wallet.Emulator.Wallet                                as EM
import           Wallet.Rollup.Render                                  (showBlockchain)

tests :: TestTree
tests = testGroup "showBlockchain"
     [ goldenVsString
          "renders a crowdfunding scenario sensibly"
          "test/Spec/renderCrowdfunding.txt"
          (render (crowdfunding theCampaign) successfulCampaign)
     , goldenVsString
          "renders a guess scenario sensibly"
          "test/Spec/renderGuess.txt"
          (render game guessTrace)
     , goldenVsString
          "renders a vesting scenario sensibly"
          "test/Spec/renderVesting.txt"
          (render (vestingContract Spec.Vesting.vesting) Spec.Vesting.retrieveFundsTrace)
     ]

render
    :: ( ContractRow s )
    => Contract s T.Text a
    -> ContractTrace s T.Text (EmulatorAction (TraceError T.Text)) a ()
    -> IO ByteString
render con trace = do
    let (result, EmulatorState{ _chainState = cs, _walletClientStates = wallets}) = runTrace con trace
    let walletKeys = flip fmap (Map.keys wallets) $ \w -> (pubKeyHash $ EM.walletPubKey w, w)
    case result of
        Left err -> assertFailure $ show err
        Right _ ->
            case showBlockchain walletKeys (EM._chainNewestFirst cs) of
                Left err       -> assertFailure $ show err
                Right rendered -> pure . LBS.fromStrict . encodeUtf8 $ rendered

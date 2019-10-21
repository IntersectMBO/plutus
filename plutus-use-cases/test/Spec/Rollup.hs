module Spec.Rollup where


import           Data.ByteString.Lazy                                  (ByteString)
import qualified Data.ByteString.Lazy                                  as LBS
import qualified Data.Map                                              as Map
import           Data.Text.Encoding                                    (encodeUtf8)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Trace
import           Ledger

import           Language.PlutusTx.Coordination.Contracts.CrowdFunding
import           Language.PlutusTx.Coordination.Contracts.Game

import           Test.Tasty                                            (TestTree, testGroup)
import           Test.Tasty.Golden                                     (goldenVsString)
import           Test.Tasty.HUnit                                      (assertFailure)
import           Wallet.Emulator.Types
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
     ]

render
    :: Contract s a
    -> ContractTrace s EmulatorAction a ()
    -> IO ByteString
render con trace = do
    let (result, EmulatorState{_chainNewestFirst=blockchain, _walletStates=wallets}) = runTrace con trace
    let walletKeys = flip fmap (Map.toList wallets) $ \(w, ws) -> (toPublicKey (_ownPrivateKey ws), w)
    let resultBlockchain = flip (fmap . fmap) blockchain $ \tx -> (hashTx tx, tx)
    case result of
        Left err -> assertFailure $ show err
        Right _ ->
            case showBlockchain walletKeys resultBlockchain of
                Left err       -> assertFailure $ show err
                Right rendered -> pure . LBS.fromStrict . encodeUtf8 $ rendered

{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Main(main) where

import           Data.Either                                         (isLeft, isRight)
import           Hedgehog                                            (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen                                        as Gen
import qualified Hedgehog.Range                                      as Range
import           Lens.Micro
import           Test.Tasty
import           Test.Tasty.Hedgehog                                 (testProperty)

import           Wallet.API                                          (PubKey (..))
import           Wallet.Emulator                                     hiding (Value)
import           Wallet.Generators                                   (Mockchain (..))
import qualified Wallet.Generators                                   as Gen

import           Language.Plutus.Coordination.Contracts.CrowdFunding (Campaign (..), CampaignActor, CampaignPLC (..),
                                                                      contribute)
import           Language.Plutus.Coordination.Plutus                 (Value)
import           Language.Plutus.CoreToPLC.Plugin                    (plc)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "use cases" [
    testGroup "crowdfunding" [
        testProperty "make a contribution" makeContribution
        ]
    ]

-- | Example campaign
c1 :: CampaignPLC
c1 = CampaignPLC $ plc Campaign {
    campaignDeadline = 10,
    campaignTarget   = 1000,
    campaignCollectionDeadline =  15,
    campaignOwner              = PubKey 1
    }

-- | Lock a transaction's outputs with the crowdfunding validator
--   script.
contrib :: Wallet -> CampaignPLC -> Value -> Trace [Tx]
contrib w c v = walletAction w $ contribute c v

-- | Generate a transaction that contributes some funds to a campaign.
--   NOTE: This doesn't actually run the validation script. The script
--         will be run when the funds are retrieved (TBD)
makeContribution :: Property
makeContribution = property $ do
    m <- forAll Gen.genMockchain
    txn <- forAll $ Gen.genValidTransaction m
    let (result, st) = Gen.runTrace m $ contrib (Wallet 1) c1 600 >> blockchainActions
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)


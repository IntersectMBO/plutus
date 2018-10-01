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

import           Language.Plutus.Coordination.Contracts.CrowdFunding (Campaign (..), CampaignActor,
                                                                      contribute)
import           Language.Plutus.Coordination.Plutus                 (Value)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "use cases" [
    testGroup "crowdfunding" [
        testProperty "make a contribution" makeContribution
        ]
    ]

-- | Lock a transaction's outputs with the crowdfunding validator
--   script.
contrib :: Campaign -> Trace [Tx]
contrib c = let w = Wallet 1 in walletAction w $ contribute c 1000

-- | Generate a transaction that contributes some funds to a campaign.
--   NOTE: This doesn't actually run the validation script. The script
--         will be run when the funds are retrieved (TBD)
makeContribution :: Property
makeContribution = property $ do
    m <- forAll Gen.genMockchain
    txn <- forAll $ Gen.genValidTransaction m
    let cmp = Campaign {
        campaignDeadline = 10,
        campaignTarget   = 1000,
        campaignCollectionDeadline = 15,
        campaignOwner = PubKey 1
        }
        (result, st) = Gen.runTrace m $ contrib cmp >> blockchainActions
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)


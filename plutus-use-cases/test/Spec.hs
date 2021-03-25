{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Auction
import qualified Spec.Crowdfunding
import qualified Spec.Currency
import qualified Spec.ErrorHandling
import qualified Spec.Escrow
import qualified Spec.Future
import qualified Spec.Game
import qualified Spec.GameStateMachine
-- import qualified Spec.MultiSig
import qualified Spec.DynamicLogic.RegistryModel
import qualified Spec.MultiSigStateMachine
import qualified Spec.PingPong
import qualified Spec.Prism
import qualified Spec.PubKey
import qualified Spec.RPC
import qualified Spec.Rollup
import qualified Spec.Stablecoin
import qualified Spec.TokenAccount
import qualified Spec.Vesting
import           Test.Tasty
import           Test.Tasty.Hedgehog             (HedgehogTestLimit (..))

main :: IO ()
main = defaultMain tests

-- | Number of successful tests for each hedgehog property.
--   The default is 100 but we use a smaller number here in order to speed up
--   the test suite.
--
limit :: HedgehogTestLimit
limit = HedgehogTestLimit (Just 5)

tests :: TestTree
tests = localOption limit $ testGroup "use cases" [
    Spec.Crowdfunding.tests,
    Spec.Vesting.tests,
    Spec.ErrorHandling.tests,
    Spec.Future.tests,
    Spec.Game.tests,
    -- disable temporarily, because we need to adopt the signing API
    -- Spec.MultiSig.tests,
    Spec.MultiSigStateMachine.tests,
    Spec.Currency.tests,
    Spec.PubKey.tests,
    Spec.Escrow.tests,
    Spec.GameStateMachine.tests,
    Spec.Rollup.tests,
    Spec.TokenAccount.tests,
    Spec.PingPong.tests,
    Spec.RPC.tests,
    Spec.Prism.tests,
    Spec.Stablecoin.tests,
    Spec.Auction.tests,
    Spec.DynamicLogic.RegistryModel.tests
    ]

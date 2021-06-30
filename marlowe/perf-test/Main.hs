{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

{-

# About this file

This is an entrypoint for testing a performance issue. It runs a specific
scenario n times.

Here's how it's been used:

1. Just run it to print times at the end:

> cabal run exe:marlowe-pab-perf-test -- 1

2.  Run it with profiling enabled to get `.prof` file that you can investigate
with `ghc-prof-flamegraph` (https://github.com/fpco/ghc-prof-flamegraph):

> cabal run exe:marlowe-pab-perf-test -- +RTS -p -RTS 1

3. Run lots of different iterations, and compare them:

> cabal run exe:marlowe-pab-perf-test -- +RTS -p -RTS 1
> ...
> cabal run exe:marlowe-pab-perf-test -- +RTS -p -RTS 5
> ...
> cabal run exe:marlowe-pab-perf-test -- +RTS -p -RTS 15
> ...
> cabal run exe:marlowe-pab-perf-test -- +RTS -p -RTS 50
> ...

Important Notes:

- Uniswap is commented out (in plutus-use-cases) as there is a plugin error if
  it's not!

- You **must** enter a nix shell with `enableHaskellProfiling` set to true, if you intend
  to generate profile output; like so:

> nix-shell --arg enableHaskellProfiling true

For this purpose, I also have the following `cabal.project.local` file:

```
> cat cabal.project.local
package marlowe
  profiling: True
  ghc-options: -fprof-auto
```

-}

module Main where

import           Control.Monad                       (forM, guard, void)
import           Control.Monad.Freer                 (Eff, Member, interpret, type (~>))
import           Control.Monad.Freer.Error           (Error)
import           Control.Monad.Freer.Extras.Log      (LogMsg)
import           Control.Monad.IO.Class              (MonadIO (..))
import           Data.Aeson                          (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import qualified Data.Aeson                          as JSON
import           Data.Aeson.Types                    (prependFailure)
import qualified Data.Aeson.Types                    as JSON
import qualified Data.Map                            as Map
import           Data.Maybe                          (listToMaybe)
import           Data.Text.Prettyprint.Doc           (Pretty (..), viaShow)
import           GHC.Generics                        (Generic)
import qualified Language.Marlowe.Client             as Marlowe
import           Language.Marlowe.Semantics          (Action (..), Case (..), Contract (..), MarloweParams, Party (..),
                                                      Payee (..), Value (..))
import qualified Language.Marlowe.Semantics          as Marlowe
import           Language.Marlowe.Util               (ada)
import           Ledger                              (PubKeyHash, Slot, pubKeyHash)
import qualified Ledger.Value                        as Val
import           Plutus.PAB.Effects.Contract         (ContractEffect (..))
import           Plutus.PAB.Effects.Contract.Builtin (Builtin, SomeBuiltin (..))
import qualified Plutus.PAB.Effects.Contract.Builtin as Builtin
import           Plutus.PAB.Monitoring.PABLogMsg     (PABMultiAgentMsg)
import           Plutus.PAB.Simulator                (SimulatorEffectHandlers)
import qualified Plutus.PAB.Simulator                as Simulator
import           Plutus.PAB.Types                    (PABError (..))
import qualified Plutus.PAB.Webserver.Server         as PAB.Server
import qualified PlutusTx.AssocMap                   as AssocMap
import           System.CPUTime                      (getCPUTime)
import           System.Environment                  (getArgs)
import           Text.Read                           (readMaybe)

main :: IO ()
main = do
  -- Run like `cabal run exe:marlowe-pab-perf-test -- +RTS -p -RTS 5`
  -- to run for 5 iterations.
  iterations <- read @Int . head <$> getArgs

  r <- Simulator.runSimulationWith handlers $ do
    Simulator.logString @(Builtin Marlowe) "Starting marlowe PAB webserver on port 8080. Press enter to exit."
    shutdown <- PAB.Server.startServerDebug
    xs <- forM [1..iterations] $ const $ timeIt marloweSteps
    let times = map fst xs
        avg   = sum times / fromIntegral (length times)
    shutdown
    return (avg, times)

  case r of
    Right (avg, times) -> do
      putStrLn $ "*************************** DONE ***************************"
      putStrLn $ "Average:          " ++ show avg
      putStrLn $ "Individual Times: " ++ show times
    Left e -> do
      putStrLn $ "**** Finished with error!"
      putStrLn $ show e

marloweSteps = do
    (newWallet, newPubKey) <- Simulator.addWallet @(Builtin Marlowe)
    Simulator.logString @(Builtin Marlowe) "Created new wallet"
    walletCompanionId <- Simulator.activateContract newWallet WalletCompanion
    Simulator.logString @(Builtin Marlowe) "Activated companion contract"
    marloweContractId <- Simulator.activateContract newWallet MarloweApp
    Simulator.logString @(Builtin Marlowe) "Activated marlowe contract"

    void $ Simulator.waitNSlots 10

    let args = let h = (pubKeyHash newPubKey) in createArgs h h
    void $ Simulator.callEndpointOnInstance marloweContractId "create" args

    followerId <- Simulator.activateContract newWallet MarloweFollower
    Simulator.logString @(Builtin Marlowe) "Activated marlowe follower"

    mp <- Simulator.waitForState @(Builtin Marlowe) extractMarloweParams walletCompanionId
    Simulator.logString @(Builtin Marlowe) $ "Found marlowe params: " <> show mp

    -- TODO: Try with follow stuff too?
    -- _ <- Simulator.waitForEndpoint followerId "follow"
    -- Simulator.logString @(Builtin Marlowe) $ "Calling endpoint on marlowe follow"
    -- _ <- Simulator.callEndpointOnInstance followerId "follow" mp

    -- followState <- Simulator.waitForState @(Builtin Marlowe) extractFollowState followerId

    -- Simulator.logString @(Builtin Marlowe) $ "Follow state: " <> show followState

timeIt :: MonadIO m => m a -> m (Double, a)
timeIt io = do
    start <- liftIO getCPUTime
    a     <- io
    end   <- liftIO getCPUTime
    let t = fromIntegral (end - start) * 1e-12
    return (t, a)

extractMarloweParams :: JSON.Value -> Maybe MarloweParams
extractMarloweParams vl = do
    (Marlowe.CompanionState s) <- either (const Nothing) Just (JSON.parseEither JSON.parseJSON vl)
    (params, _) <- listToMaybe $ Map.toList s
    pure params

extractFollowState :: JSON.Value -> Maybe Marlowe.ContractHistory
extractFollowState vl = do
    s <- either (const Nothing) Just (JSON.parseEither JSON.parseJSON vl)
    guard (not $ Marlowe.isEmpty s)
    pure s

createArgs :: PubKeyHash -> PubKeyHash -> (AssocMap.Map Val.TokenName PubKeyHash, Marlowe.Contract)
createArgs investor issuer = (tokenNames, zcb) where
    tokenNames = AssocMap.fromList [("Investor", investor), ("Issuer", issuer)]
    issuerAcc = Role "Issuer"
    investorAcc = Role "Investor"
    zcb = When
            [ Case
                (Deposit issuerAcc issuerAcc ada (Constant 850))
                (Pay issuerAcc (Account investorAcc) ada (Constant 850)
                    (When
                        [ Case (Deposit issuerAcc investorAcc ada (Constant 1000)) Close
                        ] (26936589 :: Slot) Close
                    )
                )
            ]
            (26936589 :: Slot) Close

data Marlowe =
    MarloweApp -- the main marlowe contract
    | WalletCompanion -- wallet companion contract
    | MarloweFollower -- follower contrat
    deriving (Eq, Ord, Show, Read, Generic)

instance ToJSON Marlowe where
    toJSON k = object ["tag" .= show k]

instance FromJSON Marlowe where
    parseJSON = withObject "Marlowe" $ \m -> do
        (tg :: String) <- m .: "tag"
        case readMaybe tg of
            Just tg' -> pure tg'
            _        -> prependFailure "parsing Marlowe failed, " (fail $ "unexpected tag " <> tg)

instance Pretty Marlowe where
    pretty = viaShow
handleMarloweContract ::
    ( Member (Error PABError) effs
    , Member (LogMsg (PABMultiAgentMsg (Builtin Marlowe))) effs
    )
    => ContractEffect (Builtin Marlowe)
    ~> Eff effs
handleMarloweContract = Builtin.handleBuiltin getSchema getContract where
    getSchema = const []
    getContract = \case
          MarloweApp      -> SomeBuiltin Marlowe.marlowePlutusContract
          WalletCompanion -> SomeBuiltin Marlowe.marloweCompanionContract
          MarloweFollower -> SomeBuiltin Marlowe.marloweFollowContract

handlers :: SimulatorEffectHandlers (Builtin Marlowe)
handlers =
    Simulator.mkSimulatorHandlers @(Builtin Marlowe) [MarloweApp]
    $ interpret handleMarloweContract

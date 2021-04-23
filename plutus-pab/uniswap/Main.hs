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
module Main
    ( main
    ) where

import           Control.Monad                           (forM, void)
import           Control.Monad.Freer                     (Eff, Member, interpret, type (~>))
import           Control.Monad.Freer.Error               (Error)
import           Control.Monad.IO.Class                  (MonadIO (..))
import           Data.Aeson                              (FromJSON, Result (..), ToJSON, encode, fromJSON)
import qualified Data.Map.Strict                         as Map
import qualified Data.Monoid                             as Monoid
import qualified Data.Semigroup                          as Semigroup
import           Data.Text                               (Text)
import           Data.Text.Prettyprint.Doc               (Pretty (..), viaShow)
import           GHC.Generics                            (Generic)
import           Ledger.Ada                              (adaSymbol, adaToken)
import           Plutus.Contract
import qualified Plutus.Contracts.Currency               as Currency
import qualified Plutus.Contracts.Uniswap                as Uniswap
import           Plutus.PAB.Effects.Contract             (ContractEffect (..))
import           Plutus.PAB.Effects.Contract.Builtin     (Builtin, SomeBuiltin (..), type (.\\))
import qualified Plutus.PAB.Effects.Contract.Builtin     as Builtin
import           Plutus.PAB.Effects.ContractTest.Uniswap as US
import           Plutus.PAB.Simulator                    (SimulatorEffectHandlers)
import qualified Plutus.PAB.Simulator                    as Simulator
import           Plutus.PAB.Types                        (PABError (..))
import qualified Plutus.PAB.Webserver.Server             as PAB.Server
import           Prelude                                 hiding (init)
import           Wallet.Emulator.Types                   (Wallet (..))


main :: IO ()
main = void $ Simulator.runSimulationWith handlers $ do
    Simulator.logString @(Builtin UniswapContracts) "Starting Uniswap PAB webserver on port 8080. Press enter to exit."
    shutdown <- PAB.Server.startServerDebug

    cidInit  <- Simulator.activateContract (Wallet 1) Init
    cs       <- flip Simulator.waitForState cidInit $ \json -> case fromJSON json of
                    Success (Just (Semigroup.Last cur)) -> Just $ Currency.currencySymbol cur
                    _                                   -> Nothing
    _        <- Simulator.waitUntilFinished cidInit

    Simulator.logString @(Builtin UniswapContracts) $ "Initialization finished. Minted: " ++ show cs

    let coins = Map.fromList [(tn, Uniswap.mkCoin cs tn) | tn <- tokenNames]
        ada   = Uniswap.mkCoin adaSymbol adaToken

    cidStart <- Simulator.activateContract (Wallet 1) UniswapStart
    us       <- flip Simulator.waitForState cidStart $ \json -> case (fromJSON json :: Result (Monoid.Last (Either Text Uniswap.Uniswap))) of
                    Success (Monoid.Last (Just (Right us))) -> Just us
                    _                                       -> Nothing
    Simulator.logString @(Builtin UniswapContracts) $ "Uniswap instance created: " ++ show us

    cids <- fmap Map.fromList $ forM wallets $ \w -> do
        cid <- Simulator.activateContract w $ UniswapUser us
        Simulator.logString @(Builtin UniswapContracts) $ "Uniswap user contract started for " ++ show w
        _ <- Simulator.callEndpointOnInstance cid "funds" ()
        v <- flip Simulator.waitForState cid $ \json -> case (fromJSON json :: Result (Monoid.Last (Either Text Uniswap.UserContractState))) of
                Success (Monoid.Last (Just (Right (Uniswap.Funds v)))) -> Just v
                _                                                      -> Nothing
        Simulator.logString @(Builtin UniswapContracts) $ "initial funds in wallet " ++ show w ++ ": " ++ show v
        return (w, cid)

    let cp = Uniswap.CreateParams ada (coins Map.! "A") 100000 500000
    Simulator.logString @(Builtin UniswapContracts) $ "creating liquidity pool: " ++ show (encode cp)
    _  <- Simulator.callEndpointOnInstance (cids Map.! Wallet 2) "create" cp
    flip Simulator.waitForState (cids Map.! Wallet 2) $ \json -> case (fromJSON json :: Result (Monoid.Last (Either Text Uniswap.UserContractState))) of
        Success (Monoid.Last (Just (Right Uniswap.Created))) -> Just ()
        _                                                    -> Nothing
    Simulator.logString @(Builtin UniswapContracts) "liquidity pool created"

    _ <- liftIO getLine
    shutdown

data UniswapContracts =
      Init
    | UniswapStart
    | UniswapUser Uniswap.Uniswap
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty UniswapContracts where
    pretty = viaShow

handleUniswapContract ::
    ( Member (Error PABError) effs
    )
    => ContractEffect (Builtin UniswapContracts)
    ~> Eff effs
handleUniswapContract = Builtin.handleBuiltin getSchema getContract where
  getSchema = \case
    UniswapUser _ -> Builtin.endpointsToSchemas @(Uniswap.UniswapUserSchema .\\ BlockchainActions)
    UniswapStart  -> Builtin.endpointsToSchemas @(Uniswap.UniswapOwnerSchema .\\ BlockchainActions)
    Init          -> Builtin.endpointsToSchemas @Empty
  getContract = \case
    UniswapUser us -> SomeBuiltin $ Uniswap.userEndpoints us
    UniswapStart   -> SomeBuiltin Uniswap.ownerEndpoint
    Init           -> SomeBuiltin US.initContract

handlers :: SimulatorEffectHandlers (Builtin UniswapContracts)
handlers =
    Simulator.mkSimulatorHandlers @(Builtin UniswapContracts) [] -- [Init, UniswapStart, UniswapUser ???]
    $ interpret handleUniswapContract

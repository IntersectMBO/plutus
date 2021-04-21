{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
module Main(main) where

import           Control.Monad                       (void)
import           Control.Monad.Freer                 (Eff, Member, interpret, type (~>))
import           Control.Monad.Freer.Error           (Error)
import           Control.Monad.Freer.Extras.Log      (LogMsg)
import           Control.Monad.IO.Class              (MonadIO (..))
import           Data.Aeson                          (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc           (Pretty (..), viaShow)
import           GHC.Generics                        (Generic)
import qualified Language.Marlowe.Client             as Marlowe
import           Plutus.PAB.Effects.Contract         (ContractEffect (..))
import           Plutus.PAB.Effects.Contract.Builtin (Builtin, SomeBuiltin (..))
import qualified Plutus.PAB.Effects.Contract.Builtin as Builtin
import           Plutus.PAB.Monitoring.PABLogMsg     (PABMultiAgentMsg)
import           Plutus.PAB.Simulator                (SimulatorEffectHandlers)
import qualified Plutus.PAB.Simulator                as Simulator
import           Plutus.PAB.Types                    (PABError (..))
import qualified Plutus.PAB.Webserver.Server         as PAB.Server
import           Wallet.Emulator.Types               (Wallet (..))

main :: IO ()
main = void $ Simulator.runSimulationWith handlers $ do
    Simulator.logString @(Builtin Marlowe) "Starting marlowe PAB webserver on port 8080. Press enter to exit."
    shutdown <- PAB.Server.startServerDebug
    void $ Simulator.activateContract (Wallet 1) MarloweApp
    -- You can add simulator actions here:
    -- Simulator.callEndpointOnInstance
    -- Simulator.observableState
    -- etc.
    -- That way, the simulation gets to a predefined state and you don't have to
    -- use the HTTP API for setup.
    void $ liftIO getLine
    shutdown

data Marlowe =
    MarloweApp -- the main marlowe contract
    | WalletCompanion -- TODO: actually implement this!
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty Marlowe where
    pretty = viaShow
handleMarloweContract ::
    ( Member (Error PABError) effs
    , Member (LogMsg (PABMultiAgentMsg (Builtin Marlowe))) effs
    )
    => ContractEffect (Builtin Marlowe)
    ~> Eff effs
handleMarloweContract = Builtin.handleBuiltin getSchema getContract where
    getSchema = const [] -- TODO: replace with proper schemas using Builtin.endpointsToSchemas (missing some instances currently)
    getContract = \case
        MarloweApp      -> SomeBuiltin Marlowe.marlowePlutusContract
        WalletCompanion -> error "wallet companion not implemented"

handlers :: SimulatorEffectHandlers (Builtin Marlowe)
handlers =
    Simulator.mkSimulatorHandlers @(Builtin Marlowe) [MarloweApp]
    $ interpret handleMarloweContract

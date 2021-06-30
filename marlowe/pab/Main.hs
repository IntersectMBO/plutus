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
module Main(main, handlers) where

import           Control.Monad                       (void)
import           Control.Monad.Freer                 (Eff, Member, interpret, type (~>))
import           Control.Monad.Freer.Error           (Error)
import           Control.Monad.Freer.Extras.Log      (LogMsg)
import           Control.Monad.IO.Class              (MonadIO (..))
import           Data.Aeson                          (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import           Data.Aeson.Types                    (prependFailure)
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
import           Text.Read                           (readMaybe)

main :: IO ()
main = void $ Simulator.runSimulationWith handlers $ do
     Simulator.logString @(Builtin Marlowe) "Starting marlowe PAB webserver on port 8080. Press enter to exit."
     shutdown <- PAB.Server.startServerDebug
     void $ liftIO getLine
     shutdown

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
    getSchema = const [] -- TODO: replace with proper schemas using Builtin.endpointsToSchemas (missing some instances currently)
    getContract = \case
        MarloweApp      -> SomeBuiltin Marlowe.marlowePlutusContract
        WalletCompanion -> SomeBuiltin Marlowe.marloweCompanionContract
        MarloweFollower -> SomeBuiltin Marlowe.marloweFollowContract


handlers :: SimulatorEffectHandlers (Builtin Marlowe)
handlers =
    Simulator.mkSimulatorHandlers @(Builtin Marlowe) [MarloweApp]
    $ interpret handleMarloweContract

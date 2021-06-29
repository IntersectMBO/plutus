{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Plutus.PAB.CliSpec
    ( tests
    ) where

import qualified Cardano.BM.Configuration.Model      as CM
import           Cardano.BM.Data.Severity            (Severity (..))
import           Cardano.BM.Data.Trace               (Trace)
import           Cardano.BM.Setup                    (setupTrace_)
import qualified Cardano.ChainIndex.Types            as ChainIndex.Types
import qualified Cardano.Metadata.Types              as Metadata.Types
import qualified Cardano.Node.Types                  as Node.Types
import qualified Cardano.Wallet.Client               as Wallet.Client
import           Cardano.Wallet.Types                (WalletInfo (..))
import qualified Cardano.Wallet.Types                as Wallet.Types
import           Control.Concurrent                  (threadDelay)
import           Control.Concurrent.Async            (async, cancel)
import           Control.Concurrent.Availability     (available, newToken, starting)
import           Control.Monad                       (forM_, void, when)
import           Data.Aeson                          (FromJSON, ToJSON, toJSON)
import           Data.Coerce                         (coerce)
import           Data.Either                         (isLeft)
import           Data.Proxy                          (Proxy (Proxy))
import qualified Data.Text                           as Text
import           Data.Text.Prettyprint.Doc
import           Data.Yaml                           (decodeFileThrow)
import           GHC.Generics                        (Generic)
import           Ledger.Ada                          (lovelaceValueOf)
import           Network.HTTP.Client                 (defaultManagerSettings, newManager)
import           Plutus.Contract
import qualified Plutus.Contracts.PingPong           as PingPong
import           Plutus.PAB.App                      (StorageBackend (..))
import qualified Plutus.PAB.App                      as App
import           Plutus.PAB.Effects.Contract.Builtin (Builtin, BuiltinHandler, HasDefinitions, SomeBuiltin (..))
import qualified Plutus.PAB.Effects.Contract.Builtin as Builtin
import           Plutus.PAB.Monitoring.Config        (defaultConfig)
import qualified Plutus.PAB.Monitoring.Monitoring    as LM
import           Plutus.PAB.Monitoring.PABLogMsg     (AppMsg (..))
import           Plutus.PAB.Monitoring.Util          (PrettyObject (..), convertLog)
import           Plutus.PAB.Run.Cli                  (ConfigCommandArgs (..), runConfigCommand)
import           Plutus.PAB.Run.Command              (ConfigCommand (..), MockServerMode (..))
import           Plutus.PAB.Run.PSGenerator          (HasPSTypes (..))
import           Plutus.PAB.Types                    (Config (..))
import qualified Plutus.PAB.Types                    as PAB.Types
import           Plutus.PAB.Webserver.API            (NewAPI)
import           Plutus.PAB.Webserver.Types          (ContractActivationArgs (..))
import           Prettyprinter                       (Pretty)
import           Servant                             ((:<|>) (..))
import qualified Servant
import           Servant.Client                      (BaseUrl (..), ClientEnv, Scheme (Http), client, mkClientEnv,
                                                      runClientM)
import           Test.Tasty                          (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit
import           Wallet.Emulator.Wallet              (Wallet (..))
import           Wallet.Types                        (ContractInstanceId (..))

tests :: TestTree
tests =
  testGroup "Plutus.PAB.Run.Cli"
    [ restoreContractStateTests
    ]

data TestingContracts = PingPong
  deriving (Eq, Ord, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

instance HasDefinitions TestingContracts where
  getDefinitions = [ PingPong ]
  getSchema _    = Builtin.endpointsToSchemas @PingPong.PingPongSchema
  getContract _  = SomeBuiltin PingPong.simplePingPong

instance HasPSTypes TestingContracts where
  psTypes _ = undefined

instance Pretty TestingContracts where
  pretty = viaShow


-- | Bump all the default ports, and any other needed things so that we
-- can run two PABs side-by-side.
bumpConfig
  :: Int       -- ^ Bump to add to the ports. Make sure there is no overlap!
  -> Text.Text -- ^ In-memory database name
  -> Config    -- ^ Config to bump.
  -> Config    -- ^ Bumped config!
bumpConfig x dbName conf@Config{ pabWebserverConfig   = p@PAB.Types.WebserverConfig{PAB.Types.baseUrl=p_u}
                               , walletServerConfig   = w@Wallet.Types.WalletConfig{Wallet.Types.baseUrl=w_u}
                               , nodeServerConfig     = n@Node.Types.MockServerConfig{Node.Types.mscBaseUrl=n_u,Node.Types.mscSocketPath=soc}
                               , chainIndexConfig     = c@ChainIndex.Types.ChainIndexConfig{ChainIndex.Types.ciBaseUrl=c_u}
                               , metadataServerConfig = m@Metadata.Types.MetadataConfig{Metadata.Types.mdBaseUrl=m_u}
                               , dbConfig             = db@PAB.Types.DbConfig{PAB.Types.dbConfigFile=dbFile}
                               } = newConf
  where
    bump (BaseUrl scheme url port path) = BaseUrl scheme url (port + x) path
    newConf
      = conf { pabWebserverConfig   = p { PAB.Types.baseUrl          = bump p_u }
             , walletServerConfig   = w { Wallet.Types.baseUrl       = coerce $ bump $ coerce w_u }
             , nodeServerConfig     = n { Node.Types.mscBaseUrl      = bump n_u, Node.Types.mscSocketPath = soc ++ "." ++ show x }
             , chainIndexConfig     = c { ChainIndex.Types.ciBaseUrl = coerce $ bump $ coerce c_u }
             , metadataServerConfig = m { Metadata.Types.mdBaseUrl   = bump m_u }
             , dbConfig             = db { PAB.Types.dbConfigFile    = "file::" <> dbName <> "?mode=memory&cache=shared" }
             }

startPab :: Config -> IO ()
startPab pabConfig = do
  logConfig <- defaultConfig

  CM.setMinSeverity logConfig Error

  (trace :: Trace IO (PrettyObject (AppMsg (Builtin a))), switchboard) <- setupTrace_ logConfig "pab"

  -- Ensure the db is set up
  App.migrate (convertLog (PrettyObject . PABMsg) trace) (dbConfig pabConfig)

  -- Spin up the servers
  let cmd = ForkCommands
              [ MockNode WithMockServer
              , ChainIndex
              , Metadata
              , MockWallet
              , PABWebserver
              ]

  let mkArgs availability = ConfigCommandArgs
                { ccaTrace = convertLog PrettyObject trace
                , ccaLoggingConfig = logConfig
                , ccaPABConfig = pabConfig
                , ccaAvailability = availability
                , ccaStorageBackend = BeamSqliteBackend
                }

  args <- mkArgs <$> newToken

  let handler = Builtin.handleBuiltin @TestingContracts

  async . void $ runConfigCommand handler args cmd

  -- Wait for them to be started
  threadDelay $ 10 * 1000000

getClientEnv :: Config -> IO ClientEnv
getClientEnv pabConfig = do
  manager <- newManager defaultManagerSettings

  let newApiUrl = PAB.Types.baseUrl (pabWebserverConfig pabConfig)

  pure $ mkClientEnv manager newApiUrl

startPingPongContract :: Config -> IO ContractInstanceId
startPingPongContract pabConfig = do
  apiClientEnv <- getClientEnv pabConfig

  let ca = ContractActivationArgs
                { caID     = PingPong
                , caWallet = Wallet 1
                }

  let (activateContract :<|> instance' :<|> _) = client (Proxy @(NewAPI TestingContracts Integer))

  eci <- runClientM (activateContract ca) apiClientEnv

  case eci of
    Left e   -> error $ "Error starting contract: " <> show e
    Right ci -> pure ci


-- | Tag whether or not we expect the calls to succeed.
data EndpointCall = Succeed String
                  | Fail String
ep :: EndpointCall -> String
ep (Succeed s) = s
ep (Fail s)    = s

runPabInstanceEndpoints :: Config -> ContractInstanceId -> [EndpointCall] -> IO ()
runPabInstanceEndpoints pabConfig instanceId endpoints = do
  apiClientEnv <- getClientEnv pabConfig

  let activateContract :<|> instance' :<|> _ = client (Proxy @(NewAPI TestingContracts Integer))
  let status' :<|> endpoint :<|> stop' = instance' . Text.pack . show . unContractInstanceId $ instanceId

  forM_ endpoints $ \e -> do
    x <- runClientM (endpoint (ep e) (toJSON ())) apiClientEnv
    case e of
      Succeed _ -> do
          assertEqual "Got the right thing back from the API" (Right ()) x
      Fail _ -> do
          assertBool "Endpoint call succeeded (it should've failed.)" (isLeft x)


restoreContractStateTests :: TestTree
restoreContractStateTests =
  testGroup "restoreContractState scenarios"
    [ testCase "Can init,pong,ping in one PAB instance" $ do
        -- This isn't testing anything related to restoring state; but simply
        -- provides evidence that if the subsequent tests _fail_, then that is
        -- an genuine error.
        pabConfig <- decodeFileThrow @IO "./test/full/testing-plutus-pab.yaml"
        startPab pabConfig
        ci <- startPingPongContract pabConfig
        runPabInstanceEndpoints pabConfig ci (map Succeed ["initialise", "pong", "ping"])

    , testCase "PingPong contract state is maintained across PAB instances" $ do
        -- We'll check the following: Init, Pong, <STOP>, <RESTART>, Ping works.
        pabConfig <- bumpConfig 10 "db1" <$> decodeFileThrow @IO "./test/full/testing-plutus-pab.yaml"
        startPab pabConfig
        ci <- startPingPongContract pabConfig

        -- Run init, pong on one pab
        runPabInstanceEndpoints pabConfig ci (map Succeed ["initialise", "pong"])

        -- Then, check 'ping' works on a different PAB instance (that will
        -- have restored from the same DB.)
        let newConfig = bumpConfig 10 "db1" pabConfig
        startPab newConfig

        runPabInstanceEndpoints newConfig ci [Succeed "ping"]

    , testCase "PingPong contract state is NOT maintained across PAB instances with different dbs" $ do
        -- Note: We bump the ports by 100 here because the two calls above.
        -- This should mean that no matter the order of these tests, there
        -- will be no clashes.
        pabConfig <- bumpConfig 100 "db2" <$> decodeFileThrow @IO "./test/full/testing-plutus-pab.yaml"
        startPab pabConfig
        ci <- startPingPongContract pabConfig

        -- Run init, pong on one pab
        runPabInstanceEndpoints pabConfig ci (map Succeed ["initialise", "pong"])

        -- This time, "ping" should fail because we're using a different
        -- in-memory db.
        let newConfig = bumpConfig 10 "db3" pabConfig
        startPab newConfig

        runPabInstanceEndpoints newConfig ci [Fail "ping"]
    ]

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Spec.PAB.Workflow where

import           Cardano.Wallet.Client               (createWallet)
import           Cardano.Wallet.Types                (wiPubKeyHash, wiWallet)
import           Control.Concurrent.Async            (async)
import           Control.Monad                       (guard, join, void)
import qualified Data.Aeson                          as Aeson
import qualified Data.Aeson.Types                    as Aeson
import           Data.Coerce                         (coerce)
import qualified Data.Map                            as Map
import           Data.Maybe                          (listToMaybe)
import qualified Data.Text                           as Text
import qualified Language.Marlowe.Client             as Marlowe
import           Language.Marlowe.Semantics          (Action (..), Case (..), Contract (..), MarloweParams, Party (..),
                                                      Payee (..), Value (..))
import qualified Language.Marlowe.Semantics          as Marlowe
import           Language.Marlowe.Util               (ada)
import           Ledger                              (PubKeyHash, Slot)
import qualified Ledger.Value                        as Val
import           MarloweContract                     (MarloweContract (..))
import           Network.HTTP.Client                 (defaultManagerSettings, newManager)
import qualified Network.WebSockets                  as WS
import qualified Plutus.PAB.Effects.Contract.Builtin as Builtin
import           Plutus.PAB.Webserver.Client         (InstanceClient (..), PabClient (..), pabClient)
import           Plutus.PAB.Webserver.Types          (ContractActivationArgs (..))
import qualified PlutusTx.AssocMap                   as AssocMap
import           Servant.Client                      (BaseUrl (..), ClientEnv, ClientM, mkClientEnv, runClientM)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Wallet.Types                        (ContractInstanceId (..), EndpointDescription (..))


import           Network.Socket                      (withSocketsDo)

import qualified Cardano.Wallet.Types                as Wallet.Types
import           Control.Concurrent                  (threadDelay)
import           Data.Aeson                          (decode)
import           Data.ByteString.Builder             (toLazyByteString)
import           Data.Default                        (def)
import           Data.Text.Encoding                  (encodeUtf8Builder)
import           Plutus.Contract.Effects             (aeDescription)
import           Plutus.PAB.App                      (StorageBackend (..))
import           Plutus.PAB.Run                      (runWithOpts)
import           Plutus.PAB.Run.Command              (ConfigCommand (Migrate), allServices)
import           Plutus.PAB.Run.CommandParser        (AppOpts (..))
import qualified Plutus.PAB.Types                    as PAB.Types
import           Plutus.PAB.Webserver.Types          (InstanceStatusToClient (..))


startPab :: PAB.Types.Config -> IO ()
startPab pabConfig = do
  let handler = Builtin.handleBuiltin @MarloweContract
      opts = AppOpts
              { minLogLevel = Nothing
              , logConfigPath = Nothing
              , configPath = Nothing
              , runEkgServer = False
              , storageBackend = BeamSqliteBackend
              , cmd = allServices
              }

  let mc = Just pabConfig
  -- First, migrate.
  void . async $ runWithOpts handler mc (opts {cmd = Migrate})
  sleep 1

  -- Then, spin up the services.
  void . async $ runWithOpts handler mc opts
  sleep 5

sleep :: Int -> IO ()
sleep n = threadDelay $ n * 1_000_000

waitForState :: (Aeson.Value -> Maybe a) -> (InstanceStatusToClient -> Maybe a)
waitForState f = g
    where
      g (NewObservableState v) = f v
      g _                      = Nothing

waitForEndpoint :: String -> (InstanceStatusToClient -> Maybe ())
waitForEndpoint ep = g
  where
    g (NewActiveEndpoints eps) = guard (any (\aep -> coerce (aeDescription aep) == ep) eps) >> Just ()
    g _                        = Nothing

runWebSocket :: BaseUrl -> ContractInstanceId -> (InstanceStatusToClient -> Maybe a) -> IO a
runWebSocket (BaseUrl _ host port _) cid f = do
  let url = "/ws/" <> contractInstanceToString cid
  withSocketsDo
    $ WS.runClient host port (Text.unpack url)
    $ \conn ->
      let go = WS.receiveData conn >>= \msg ->
                case join (f <$> decodeFromText msg) of
                  Just a  -> pure a
                  Nothing -> go
       in go

contractInstanceToString :: ContractInstanceId -> Text.Text
contractInstanceToString  = Text.pack . show . unContractInstanceId

marloweCompanionFollowerContractExample :: IO ()
marloweCompanionFollowerContractExample = do
  manager <- newManager defaultManagerSettings

  let pabConfig = def { PAB.Types.pabWebserverConfig = def { PAB.Types.endpointTimeout = Just 30 } }
      apiUrl = PAB.Types.baseUrl (PAB.Types.pabWebserverConfig pabConfig)
      apiClientEnv = mkClientEnv manager apiUrl
      walletUrl = coerce $ Wallet.Types.baseUrl (PAB.Types.walletServerConfig pabConfig)
      walletClientEnv = mkClientEnv manager walletUrl

      PabClient{activateContract, instanceClient} = pabClient @MarloweContract @Integer

      -- This depends on the PabClient `instanceClient` route.
      callEndpointOnInstance :: Aeson.ToJSON a => ContractInstanceId -> String -> a -> ClientM ()
      callEndpointOnInstance cid ep args =
        let call = callInstanceEndpoint . instanceClient . contractInstanceToString $ cid
         in call ep $ Aeson.toJSON args

      run :: ClientEnv -> ClientM a -> IO a
      run env ca = do
        ea <- runClientM ca env
        case ea of
          Left  e -> error $ show $ e
          Right a -> pure a

      runApi    = run apiClientEnv
      runWallet = run walletClientEnv
      runWs     = runWebSocket apiUrl

  startPab pabConfig

  walletInfo <- runWallet $ createWallet

  let wallet = wiWallet walletInfo
      hash   = wiPubKeyHash walletInfo
      args   = createArgs hash hash

  companionContractId <- runApi $ activateContract $ ContractActivationArgs { caID = WalletCompanion, caWallet = wallet }
  marlowContractId    <- runApi $ activateContract $ ContractActivationArgs { caID = MarloweApp, caWallet = wallet }

  sleep 2

  runApi $ callEndpointOnInstance marlowContractId "create" args

  followerId <- runApi $ activateContract $ ContractActivationArgs { caID = MarloweFollower, caWallet = wallet }

  sleep 2

  mp <- runWs companionContractId $ waitForState extractMarloweParams

  runWs followerId $ waitForEndpoint "follow"

  runApi $ callEndpointOnInstance followerId "follow" mp

  _ <- runWs followerId $ waitForState extractFollowState

  -- We're happy if the above call completes.

  pure ()

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

decodeFromText :: Aeson.FromJSON a => Text.Text -> Maybe a
decodeFromText = decode . toLazyByteString . encodeUtf8Builder

extractMarloweParams :: Aeson.Value -> Maybe MarloweParams
extractMarloweParams vl = do
    (Marlowe.CompanionState s) <- either (const Nothing) Just (Aeson.parseEither Aeson.parseJSON vl)
    (params, _) <- listToMaybe $ Map.toList s
    pure params

extractFollowState :: Aeson.Value -> Maybe Marlowe.ContractHistory
extractFollowState vl = do
    s <- either (const Nothing) Just (Aeson.parseEither Aeson.parseJSON vl)
    guard (not $ Marlowe.isEmpty s)
    pure s

tests :: TestTree
tests = testGroup "Marlowe Workflow tests"
  [ testCase "Marlowe Follower/Companion contract scenario can be completed" $ do
      marloweCompanionFollowerContractExample
  ]

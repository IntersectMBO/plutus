{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-

PSgenerator for types from the test suite. This is needed to test
JSON deserialisation on the PS client side.

-}
module Main(main) where

import           Control.Monad                              (void)
import qualified Data.Aeson.Encode.Pretty                   as JSON
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Proxy                                 (Proxy (..))
import qualified Data.Text                                  as Text
import           Language.PureScript.Bridge                 (BridgePart, Language (Haskell), SumType, buildBridge,
                                                             defaultBridge, equal, genericShow, mkSumType,
                                                             writePSTypesWith, (<|>))
import           Language.PureScript.Bridge.CodeGenSwitches (ForeignOptions (..), genForeign)
import qualified PSGenerator.Common
import           Plutus.Contracts.Currency                  (SimpleMPS (..))
import           Plutus.PAB.Effects.Contract.ContractTest   (TestContracts (Currency, GameStateMachine))
import qualified Plutus.PAB.Simulator                       as Simulator
import qualified Plutus.PAB.Simulator.Test                  as Simulator
import qualified Plutus.PAB.Webserver.Handler               as Webserver
import           Plutus.PAB.Webserver.Types                 (ContractSignatureResponse, FullReport)
import           Servant.PureScript                         (HasBridge (..))
import           System.Environment                         (getArgs)
import           System.FilePath                            ((</>))
import           Wallet.Emulator.Wallet                     (Wallet (..))
import           Wallet.Types                               (ContractInstanceId (..))

data TestBridge

testBridge :: BridgePart
testBridge =
    PSGenerator.Common.aesonBridge <|>
    PSGenerator.Common.containersBridge <|>
    PSGenerator.Common.languageBridge <|>
    PSGenerator.Common.ledgerBridge <|>
    PSGenerator.Common.servantBridge <|>
    PSGenerator.Common.miscBridge <|>
    defaultBridge

testBridgeProxy :: Proxy TestBridge
testBridgeProxy = Proxy

instance HasBridge TestBridge where
    languageBridge _ = buildBridge testBridge

testTypes :: [SumType 'Haskell]
testTypes =
    [ (equal <*> (genericShow <*> mkSumType)) (Proxy @TestContracts) ]

main :: IO ()
main = getArgs >>= \case
    [outputDir] -> do
        writePSTypesWith
            (genForeign (ForeignOptions {unwrapSingleConstructors = True}))
            outputDir
            (buildBridge testBridge)
            testTypes
        writeTestData outputDir
    _ -> putStrLn "Usage: plutus-pab-test-psgenerator FILEPATH"

defaultWallet :: Wallet
defaultWallet = Wallet 1

writeTestData :: FilePath -> IO ()
writeTestData outputDir = do
    (fullReport, currencySchema) <-
        fmap (either (error . show) id) $ Simulator.runSimulation $ do
            currencyInstance1 <- Simulator.activateContract defaultWallet Currency
            void $ Simulator.activateContract defaultWallet Currency
            void $ Simulator.activateContract defaultWallet GameStateMachine
            void $ Simulator.waitForEndpoint currencyInstance1 "Create native token"
            void $ Simulator.callEndpointOnInstance currencyInstance1 "Create native token" SimpleMPS {tokenName = "TestCurrency", amount = 10000000000}
            void $ Simulator.waitUntilFinished currencyInstance1
            report :: FullReport TestContracts <- Webserver.getFullReport
            schema :: ContractSignatureResponse TestContracts <- Webserver.contractSchema (Text.pack $ show $ unContractInstanceId currencyInstance1)
            pure (report, schema)
    BSL.writeFile
        (outputDir </> "full_report_response.json")
        (JSON.encodePretty fullReport)
    BSL.writeFile
        (outputDir </> "contract_schema_response.json")
        (JSON.encodePretty currencySchema)


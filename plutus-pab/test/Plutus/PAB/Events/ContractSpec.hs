{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Plutus.PAB.Events.ContractSpec
    ( tests
    ) where

import           Control.Monad.Except                    (ExceptT (ExceptT), runExceptT)
import           Control.Monad.Trans.Except              (except)
import qualified Data.Aeson                              as JSON
import           Data.Bifunctor                          (first)
import qualified Data.ByteString.Char8                   as BS
import qualified Data.ByteString.Lazy                    as BSL
import           Data.Proxy                              (Proxy (Proxy))
import qualified Data.Text                               as T
import           GHC.TypeLits                            (symbolVal)
import           Plutus.Contract                         (BlockchainActions)
import           Plutus.Contract.Effects.ExposeEndpoint  (ActiveEndpoint (..),
                                                          EndpointDescription (EndpointDescription))
import qualified Plutus.Contract.Schema                  as Schema
import           Plutus.Contracts.GameStateMachine       (GameStateMachineSchema, contract)
import           Plutus.PAB.Arbitrary                    ()
import           Plutus.PAB.ContractCLI                  (Command (Initialise), runCliCommand)
import           Plutus.PAB.Events.Contract              (ContractHandlerRequest, ContractHandlersResponse,
                                                          ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import           Test.Tasty                              (TestTree, testGroup)
import           Test.Tasty.HUnit                        (assertFailure, testCase)

tests :: TestTree
tests = testGroup "Plutus.PAB.Events.Contract" [jsonTests]

jsonTests :: TestTree
jsonTests =
    testGroup
        "ToJSON/FromJSON"
        [ testCase "Decode handlers" $
          let handlers :: Schema.Handlers GameStateMachineSchema
              handlers =
                  Schema.initialise @GameStateMachineSchema @"guess" @_ $
                  ActiveEndpoint
                      { aeDescription = EndpointDescription (symbolVal (Proxy @"guess"))
                      , aeMetadata    = Nothing
                      }
              response :: Either String ContractHandlerRequest
              response = JSON.eitherDecode $ JSON.encode handlers
           in assertRight response
        , testCase "Decode contract initialisation" $ do
              v <-
                  runExceptT $ do
                      initialisationResponse <-
                          ExceptT $
                            first BS.unpack <$> runCliCommand (Proxy @BlockchainActions) (first (T.pack . show) contract) Initialise
                      result <-
                          except $ JSON.eitherDecode $ BSL.fromStrict initialisationResponse
                      pure
                          (result :: PartiallyDecodedResponse ContractHandlerRequest)
              assertRight v
        ]

assertRight :: Either String a -> IO ()
assertRight (Left err) = assertFailure err
assertRight (Right _)  = pure ()

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Plutus.PAB.Events.ContractSpec
    ( tests
    ) where

import           Control.Monad.Except                            (ExceptT (ExceptT), runExceptT)
import           Control.Monad.Trans.Except                      (except)
import qualified Data.Aeson                                      as JSON
import           Data.Bifunctor                                  (first)
import qualified Data.ByteString.Char8                           as BS
import qualified Data.ByteString.Lazy                            as BSL
import           Data.Proxy                                      (Proxy (Proxy))
import           GHC.TypeLits                                    (symbolVal)
import           Language.Plutus.Contract                        (BlockchainActions)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint (..),
                                                                  EndpointDescription (EndpointDescription))
import qualified Language.Plutus.Contract.Schema                 as Schema
import           Language.PlutusTx.Coordination.Contracts.Game   (GameSchema, game)
import           Plutus.PAB.Arbitrary                            ()
import           Plutus.PAB.ContractCLI                          (Command (Initialise), runCliCommand)
import           Plutus.PAB.Events.Contract                      (ContractHandlersResponse, PartiallyDecodedResponse)
import           Test.Tasty                                      (TestTree, testGroup)
import           Test.Tasty.HUnit                                (assertFailure, testCase)

tests :: TestTree
tests = testGroup "Plutus.PAB.Events.Contract" [jsonTests]

jsonTests :: TestTree
jsonTests =
    testGroup
        "ToJSON/FromJSON"
        [ testCase "Decode handlers" $
          let handlers :: Schema.Handlers GameSchema
              handlers =
                  Schema.initialise @GameSchema @"guess" @_ $
                  ActiveEndpoint
                      { aeDescription = EndpointDescription (symbolVal (Proxy @"guess"))
                      , aeMetadata    = Nothing
                      }
              response :: Either String ContractHandlersResponse
              response = JSON.eitherDecode $ JSON.encode handlers
           in assertRight response
        , testCase "Decode contract initialisation" $ do
              v <-
                  runExceptT $ do
                      initialisationResponse <-
                          ExceptT $
                            first BS.unpack <$> runCliCommand (Proxy @BlockchainActions) game Initialise
                      result <-
                          except $ JSON.eitherDecode $ BSL.fromStrict initialisationResponse
                      pure
                          (result :: PartiallyDecodedResponse ContractHandlersResponse)
              assertRight v
        ]

assertRight :: Either String a -> IO ()
assertRight (Left err) = assertFailure err
assertRight (Right _)  = pure ()

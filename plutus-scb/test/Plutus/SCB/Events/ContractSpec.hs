{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Plutus.SCB.Events.ContractSpec
    ( tests
    ) where

import           Control.Monad.Except                            (ExceptT (ExceptT), runExceptT)
import           Control.Monad.Trans.Except                      (except)
import qualified Data.Aeson                                      as JSON
import           Data.Bifunctor                                  (first)
import qualified Data.ByteString.Lazy.Char8                      as BSL
import           Data.Proxy                                      (Proxy (Proxy))
import           GHC.TypeLits                                    (symbolVal)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint (ActiveEndpoint),
                                                                  EndpointDescription (EndpointDescription))
import qualified Language.Plutus.Contract.Schema                 as Schema
import           Language.PlutusTx.Coordination.Contracts.Game   (GameSchema, game)
import           Plutus.SCB.Arbitrary                            ()
import           Plutus.SCB.ContractCLI                          (Command (Initialise), runCliCommand)
import           Plutus.SCB.Events.Contract                      (ContractHandlersResponse, PartiallyDecodedResponse)
import           Test.Tasty                                      (TestTree, testGroup)
import           Test.Tasty.HUnit                                (assertFailure, testCase)

tests :: TestTree
tests = testGroup "SCB.Events.Contract" [jsonTests]

jsonTests :: TestTree
jsonTests =
    testGroup
        "ToJSON/FromJSON"
        [ testCase "Decode handlers" $
          let handlers :: Schema.Handlers GameSchema
              handlers =
                  Schema.initialise @GameSchema @"guess" @_ $
                  ActiveEndpoint
                      (EndpointDescription (symbolVal (Proxy @"guess")))
              response :: Either String ContractHandlersResponse
              response = JSON.eitherDecode $ JSON.encode handlers
           in assertRight response
        , testCase "Decode contract initialisation" $ do
              v <-
                  runExceptT $ do
                      initialisationResponse <-
                          ExceptT $
                          first BSL.unpack <$> runCliCommand game Initialise
                      result <-
                          except $ JSON.eitherDecode initialisationResponse
                      pure
                          (result :: PartiallyDecodedResponse ContractHandlersResponse)
              assertRight v
        ]

assertRight :: Either String a -> IO ()
assertRight (Left err) = assertFailure err
assertRight (Right _)  = pure ()

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Plutus.SCB.Effects.ContractTest(
    TestContracts(..)
    , handleContractTest
    ) where

import           Control.Monad                                     (void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                         (Error, throwError)
import           Data.Aeson                                        as JSON
import           Data.Aeson.Types                                  as JSON
import           Data.Bifunctor                                    (Bifunctor (..))
import           Data.Row
import           Data.Text                                         (Text)
import qualified Data.Text                                         as Text
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                                      (Generic)
import           Language.Plutus.Contract                          (BlockchainActions)

import           Plutus.SCB.Effects.Contract                       (ContractCommand (..), ContractEffect (..))
import           Plutus.SCB.Events.Contract                        (ContractSCBRequest, PartiallyDecodedResponse,
                                                                    WrappedContractSCBRequest (..))
import qualified Plutus.SCB.Events.Contract                        as C
import           Plutus.SCB.Types                                  (SCBError (..))
import           Plutus.SCB.Utils                                  (render, tshow)

import           Control.Monad.Freer.Extra.Log                     (Log, logDebug)
import           Language.Plutus.Contract                          (Contract, ContractError)

import           Language.Plutus.Contract.Schema                   (Event, Handlers, Input, Output)
import           Language.Plutus.Contract.State                    (ContractRequest, ContractResponse (..))
import qualified Language.Plutus.Contract.State                    as ContractState
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Contracts.Currency
import qualified Language.PlutusTx.Coordination.Contracts.Game     as Contracts.Game
import           Playground.Schema                                 (endpointsToSchemas)

import qualified Debug.Trace                                       as Trace

data TestContracts = Game | Currency
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty TestContracts where
    pretty = viaShow

-- | A mock/test handler for 'ContractEffect'
handleContractTest ::
    (Member (Error SCBError) effs, Member Log effs)
    => Eff (ContractEffect TestContracts ': effs)
    ~> Eff effs
handleContractTest = interpret $ \case
    InvokeContract (InitContract c) -> case c of
        Game     -> doContractInit game
        Currency -> doContractInit currency
    InvokeContract (UpdateContract c p) -> case c of
        Game     -> doContractUpdate game p
        Currency -> doContractUpdate currency p
    ExportSchema t -> case t of
        Game     -> pure $ endpointsToSchemas @(Contracts.Game.GameSchema .\\ BlockchainActions)
        Currency -> pure $ endpointsToSchemas @(Contracts.Currency.CurrencySchema .\\ BlockchainActions)
    where
        game = first tshow $ Contracts.Game.game @ContractError
        currency = first tshow $ void Contracts.Currency.forgeCurrency

doContractInit ::
    forall schema effs.
    ( Member (Error SCBError) effs
    , Forall (Output schema) ToJSON
    , Forall (Input schema) ToJSON
    )
    => Contract schema Text ()
    -> Eff effs (PartiallyDecodedResponse ContractSCBRequest)
doContractInit contract = either throwError pure $ do
    value <- first OtherError $ ContractState.initialiseContract contract
    fromString $ fmap (fmap unWrappedContractSCBRequest) $ JSON.eitherDecode $ (JSON.encode value)

doContractUpdate ::
    forall schema effs.
    ( Member (Error SCBError) effs
    , AllUniqueLabels (Input schema)
    , Forall (Input schema) FromJSON
    , Forall (Input schema) ToJSON
    , Forall (Output schema) ToJSON
    , Forall (Input schema) Show
    , Member Log effs
    )
    => Contract schema Text ()
    -> ContractRequest Value
    -> Eff effs (PartiallyDecodedResponse ContractSCBRequest)
doContractUpdate contract payload = do
    logDebug "doContractUpdate"
    logDebug $ Text.pack  $ show $ Trace.traceShowId $ fmap JSON.encode payload
    request :: (ContractRequest (Event schema)) <-
        either throwError pure
        $ fromString
        $ traverse (JSON.parseEither JSON.parseJSON) payload
    logDebug . render $ "Request:" <+> pretty request
    response <-
        either (throwError . OtherError) (pure . mkResponse)
        $ ContractState.insertAndUpdateContract contract request
    logDebug . render $ "Response:" <+> pretty response
    pure response

mkResponse ::
    forall schema.
    ( Forall (Output schema) ToJSON
    , Forall (Input schema) ToJSON
    )
    => ContractResponse (Event schema) (Handlers schema)
    -> PartiallyDecodedResponse ContractSCBRequest
mkResponse ContractResponse{newState, hooks} =
    C.PartiallyDecodedResponse
        { C.newState = fmap JSON.toJSON newState
        , C.hooks    = fmap (fmap (encodeRequest @schema)) hooks
        }

encodeRequest ::
    forall schema.
    ( Forall (Output schema) ToJSON
    )
    => Handlers schema
    -> ContractSCBRequest
encodeRequest = either error unWrappedContractSCBRequest . JSON.eitherDecode . JSON.encode

fromString :: Either String a -> Either SCBError a
fromString = first (ContractCommandError 0 . Text.pack)

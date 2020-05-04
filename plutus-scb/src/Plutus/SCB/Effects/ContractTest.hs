{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Plutus.SCB.Effects.ContractTest(
    TestContracts(..)
    , handleContractTest
    , fromResumable
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
import           Plutus.SCB.Events.Contract                        (PartiallyDecodedResponse)
import           Plutus.SCB.Types                                  (SCBError (..))

import           Language.Plutus.Contract.Request                  (Contract)
import           Language.Plutus.Contract.Resumable                (ResumableError)
import           Language.Plutus.Contract.Schema                   (Input, Output)
import           Language.Plutus.Contract.Servant                  (Response, initialResponse, runUpdate)
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Contracts.Currency
import qualified Language.PlutusTx.Coordination.Contracts.Game     as Contracts.Game
import           Playground.Schema                                 (endpointsToSchemas)

data TestContracts = Game | Currency
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty TestContracts where
    pretty = viaShow

-- | A mock/test handler for 'ContractEffect'
handleContractTest ::
    (Member (Error SCBError) effs)
    => Eff (ContractEffect TestContracts ': effs)
    ~> Eff effs
handleContractTest = interpret $ \case
    InvokeContract (InitContract c) -> case c of
        Game     -> doContractInit Contracts.Game.game
        Currency -> doContractInit (void Contracts.Currency.forgeCurrency)
    InvokeContract (UpdateContract c p) -> case c of
        Game     -> doContractUpdate Contracts.Game.game p
        Currency -> doContractUpdate (void Contracts.Currency.forgeCurrency) p
    ExportSchema t -> case t of
        Game     -> pure $ endpointsToSchemas @(Contracts.Game.GameSchema .\\ BlockchainActions)
        Currency -> pure $ endpointsToSchemas @(Contracts.Currency.CurrencySchema .\\ BlockchainActions)

doContractInit ::
    forall schema effs.
    ( Member (Error SCBError) effs
    , AllUniqueLabels (Output schema)
    , Forall (Output schema) Monoid
    , Forall (Output schema) Semigroup
    , Forall (Output schema) ToJSON
    , Forall (Input schema) ToJSON
    )
    => Contract schema Text ()
    -> Eff effs (Either Text PartiallyDecodedResponse)
doContractInit contract = either throwError pure $ do
    value <- fromResumable $ initialResponse contract
    fromString $ JSON.eitherDecode (JSON.encode (Right value :: Either Text (Response schema)))


doContractUpdate ::
    forall schema effs.
    ( Member (Error SCBError) effs
    , AllUniqueLabels (Input schema)
    , Forall (Input schema) FromJSON
    , Forall (Input schema) ToJSON
    , AllUniqueLabels (Output schema)
    , Forall (Output schema) Monoid
    , Forall (Output schema) Semigroup
    , Forall (Output schema) ToJSON
    )
    => Contract schema Text ()
    -> Value
    -> Eff effs (Either Text PartiallyDecodedResponse)
doContractUpdate contract payload = either throwError pure $ do
    request <- fromString $ JSON.parseEither JSON.parseJSON payload
    value <- fromResumable $ runUpdate contract request
    fromString $ JSON.eitherDecode (JSON.encode (Right value :: Either Text (Response schema)))

fromString :: Either String a -> Either SCBError a
fromString = first (ContractCommandError 0 . Text.pack)

fromResumable :: Either (ResumableError Text) a -> Either SCBError a
fromResumable = first (ContractCommandError 0 . Text.pack . show)

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeOperators              #-}
module Plutus.SCB.Effects.ContractTest(
    TestContracts(..)
    , handleContractTest
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Error                     (Error, throwError)
import           Control.Monad.Freer.State
import           Data.Aeson                                    as JSON
import           Data.Aeson.Types                              as JSON
import           Data.Bifunctor                                (Bifunctor (..))
import           Data.Map                                      (Map)
import qualified Data.Map                                      as Map
import           Data.Text                                     (Text)
import qualified Data.Text                                     as Text
import           Data.Text.Prettyprint.Doc

import           Plutus.SCB.Effects.Contract                   (ContractCommand (..), ContractEffect (..))
import           Plutus.SCB.Types                              (SCBError (..))

import           Language.Plutus.Contract.Request              (Contract)
import           Language.Plutus.Contract.Resumable            (ResumableError)
import           Language.Plutus.Contract.Servant              (initialResponse, runUpdate)
import qualified Language.PlutusTx.Coordination.Contracts.Game as Contracts.Game

data TestContracts = Game | Currency
    deriving (Eq, Ord, Show)

instance Pretty TestContracts where
    pretty = viaShow

-- | A mock/test handler for 'ContractEffect'
handleContractTest ::
    (Member (Error SCBError) effs)
    => Eff (ContractEffect TestContracts ': effs)
    ~> Eff effs
handleContractTest = interpret $ \case
    InvokeContract (InitContract Game) ->
        either throwError pure $ do
            value <- fromResumable $ initialResponse Contracts.Game.game
            fromString $ JSON.eitherDecode (JSON.encode value)
    InvokeContract (UpdateContract Game payload) ->
        either throwError pure $ do
            request <- fromString $ JSON.parseEither JSON.parseJSON payload
            value <- fromResumable $ runUpdate Contracts.Game.game request
            fromString $ JSON.eitherDecode (JSON.encode value)
    InvokeContract (InitContract contractPath) ->
        throwError $ ContractNotFound (show contractPath)
    InvokeContract (UpdateContract contractPath _) ->
        throwError $ ContractNotFound (show contractPath)

fromString :: Either String a -> Either SCBError a
fromString = first (ContractCommandError 0 . Text.pack)

fromResumable :: Either (ResumableError Text) a -> Either SCBError a
fromResumable = first (ContractCommandError 0 . Text.pack . show)

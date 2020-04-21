{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeOperators    #-}
module Plutus.SCB.Effects.ContractTest(
    handleContractTest
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Error                     (Error, throwError)
import           Data.Aeson                                    as JSON
import           Data.Aeson.Types                              as JSON
import           Data.Bifunctor                                (Bifunctor (..))
import           Data.Text                                     (Text)
import qualified Data.Text                                     as Text

import           Plutus.SCB.Effects.Contract                   (ContractCommand (..), ContractEffect (..))
import           Plutus.SCB.Types                              (SCBError (..))

import           Language.Plutus.Contract.Resumable            (ResumableError)
import           Language.Plutus.Contract.Servant              (initialResponse, runUpdate)
import qualified Language.PlutusTx.Coordination.Contracts.Game as Contracts.Game

-- | A mock/test handler for 'ContractEffect'
handleContractTest ::
    (Member (Error SCBError) effs)
    => Eff (ContractEffect ': effs)
    ~> Eff effs
handleContractTest = interpret $ \case
    InvokeContract (InitContract "game") ->
        either throwError pure $ do
            value <- fromResumable $ initialResponse Contracts.Game.game
            fromString $ JSON.eitherDecode (JSON.encode value)
    InvokeContract (UpdateContract "game" payload) ->
        either throwError pure $ do
            request <- fromString $ JSON.parseEither JSON.parseJSON payload
            value <- fromResumable $ runUpdate Contracts.Game.game request
            fromString $ JSON.eitherDecode (JSON.encode value)
    InvokeContract (InitContract contractPath) ->
        throwError $ ContractNotFound contractPath
    InvokeContract (UpdateContract contractPath _) ->
        throwError $ ContractNotFound contractPath

fromString :: Either String a -> Either SCBError a
fromString = first (ContractCommandError 0 . Text.pack)

fromResumable :: Either (ResumableError Text) a -> Either SCBError a
fromResumable = first (ContractCommandError 0 . Text.pack . show)

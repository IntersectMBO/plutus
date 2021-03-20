{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Plutus.PAB.Webserver.Handler
    ( handlerNew
    , handlerOld
    -- * Reports
    , getFullReport
    , contractSchema
    ) where

import           Control.Lens                            (preview)
import           Control.Monad                           (void)
import           Control.Monad.Freer.Error               (throwError)
import qualified Data.Aeson                              as JSON
import qualified Data.Map                                as Map
import           Data.Maybe                              (mapMaybe)
import           Data.Proxy                              (Proxy (..))
import           Data.Text                               (Text)
import qualified Data.UUID                               as UUID
import           Network.WebSockets.Connection           (PendingConnection)
import           Plutus.PAB.Core                         (PABAction)
import qualified Plutus.PAB.Core                         as Core
import qualified Plutus.PAB.Effects.Contract             as Contract
import           Plutus.PAB.Events.Contract              (ContractPABRequest, _UserEndpointRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse (..))
import           Plutus.PAB.Types
import           Plutus.PAB.Webserver.API                (ContractActivationArgs (..), ContractInstanceClientState (..))
import           Plutus.PAB.Webserver.Types
import qualified Plutus.PAB.Webserver.WebSocket          as WS
import           Servant                                 ((:<|>) ((:<|>)))
import           Wallet.Emulator.Wallet                  (Wallet (..))
import           Wallet.Types                            (ContractInstanceId (..), NotificationError)

-- | Handler for the "old" API
handlerOld ::
    forall t env.
    Contract.PABContract t =>
    PABAction t env ()
    :<|> (PABAction t env (FullReport (Contract.ContractDef t))
        :<|> ((Contract.ContractDef t) -> PABAction t env ContractInstanceId)
        :<|> (Text -> PABAction t env (ContractSignatureResponse (Contract.ContractDef t))
            :<|> (String -> JSON.Value -> PABAction t env (Maybe NotificationError))
            )
        )
handlerOld =
    healthcheck
        :<|> (getFullReport
            :<|> (\def -> activateContract ContractActivationArgs{caID=def, caWallet=Wallet 1}) -- TODO: Delete "contract/activate" route without wallet argument
            :<|> byContractInstanceId
        )
    where
        byContractInstanceId :: Text -> (PABAction t env (ContractSignatureResponse (Contract.ContractDef t)) :<|> (String -> JSON.Value -> PABAction t env (Maybe NotificationError)))
        byContractInstanceId rawInstanceId =
            (parseContractId rawInstanceId >>= contractSchema) :<|> undefined


healthcheck :: forall t env. PABAction t env ()
healthcheck = pure ()

getContractReport :: forall t env. Contract.PABContract t => PABAction t env (ContractReport (Contract.ContractDef t))
getContractReport = do
    installedContracts <- Contract.getDefinitions @t
    activeContractIDs <- fmap fst . Map.toList <$> Contract.getActiveContracts @t
    crAvailableContracts <-
        traverse
            (\t -> ContractSignatureResponse t <$> Contract.exportSchema @t t)
            installedContracts
    crActiveContractStates <- traverse (\i -> Contract.getState @t i >>= \s -> pure (i, Contract.serialisableState (Proxy @t) s)) activeContractIDs
    pure ContractReport {crAvailableContracts, crActiveContractStates}

getFullReport :: forall t env. Contract.PABContract t => PABAction t env (FullReport (Contract.ContractDef t))
getFullReport = do
    contractReport <- getContractReport @t
    pure FullReport {contractReport, chainReport = emptyChainReport}

contractSchema :: forall t env. Contract.PABContract t => ContractInstanceId -> PABAction t env (ContractSignatureResponse (Contract.ContractDef t))
contractSchema contractId = Contract.getDefinition @t contractId >>= \case
    Just definition -> ContractSignatureResponse definition <$> Contract.exportSchema @t definition
    Nothing         -> throwError (ContractInstanceNotFound contractId)

parseContractId :: Text -> PABAction t env ContractInstanceId
parseContractId t =
    case UUID.fromText t of
        Just uuid -> pure $ ContractInstanceId uuid
        Nothing   -> throwError $ InvalidUUIDError t

-- | Handler for the "new" API
handlerNew ::
       forall t env.
       Contract.PABContract t =>
       (ContractActivationArgs (Contract.ContractDef t) -> PABAction t env ContractInstanceId)
            :<|> (ContractInstanceId -> PABAction t env (ContractInstanceClientState)
                                        :<|> (String -> JSON.Value -> PABAction t env ())
                                        :<|> (PendingConnection -> PABAction t env ()))
            :<|> PABAction t env [ContractInstanceClientState]
            :<|> PABAction t env [ContractSignatureResponse (Contract.ContractDef t)]
handlerNew =
        (activateContract
            :<|> (\x -> contractInstanceState x :<|> callEndpoint x :<|> WS.contractInstanceUpdates x)
            :<|> allInstanceStates
            :<|> availableContracts)

fromInternalState ::
    ContractInstanceId
    -> PartiallyDecodedResponse ContractPABRequest
    -> ContractInstanceClientState
fromInternalState i resp =
    ContractInstanceClientState
        { cicContract = i
        , cicCurrentState =
            let hks' = mapMaybe (traverse (preview _UserEndpointRequest)) (hooks resp)
            in resp { hooks = hks' }
        }

-- HANDLERS

activateContract :: forall t env. Contract.PABContract t => ContractActivationArgs (Contract.ContractDef t) -> PABAction t env ContractInstanceId
activateContract ContractActivationArgs{caID, caWallet} = do
    Core.activateContract caWallet caID

contractInstanceState :: forall t env. Contract.PABContract t => ContractInstanceId -> PABAction t env ContractInstanceClientState
contractInstanceState i = fromInternalState i . Contract.serialisableState (Proxy @t) <$> Contract.getState @t i

callEndpoint :: forall t env. ContractInstanceId -> String -> JSON.Value -> PABAction t env ()
callEndpoint a b = void . Core.callEndpointOnInstance a b

allInstanceStates :: forall t env. Contract.PABContract t => PABAction t env [ContractInstanceClientState]
allInstanceStates = do
    mp <- Contract.getActiveContracts @t
    let get i = fromInternalState i . Contract.serialisableState (Proxy @t) <$> Contract.getState @t i
    traverse get $ fst <$> Map.toList mp

availableContracts :: forall t env. Contract.PABContract t => PABAction t env [ContractSignatureResponse (Contract.ContractDef t)]
availableContracts = do
    def <- Contract.getDefinitions @t
    let mkSchema s = ContractSignatureResponse s <$> Contract.exportSchema @t s
    traverse mkSchema def


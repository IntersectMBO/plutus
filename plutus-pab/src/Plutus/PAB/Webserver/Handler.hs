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
    , walletProxy
    , walletProxyClientEnv
    -- * Reports
    , getFullReport
    , contractSchema
    ) where

import qualified Cardano.Wallet.Client                   as Wallet.Client
import           Control.Lens                            (preview)
import           Control.Monad                           ((>=>))
import           Control.Monad.Freer                     (sendM)
import           Control.Monad.Freer.Error               (throwError)
import           Control.Monad.IO.Class                  (MonadIO (..))
import qualified Data.Aeson                              as JSON
import           Data.Foldable                           (traverse_)
import qualified Data.Map                                as Map
import           Data.Maybe                              (mapMaybe)
import           Data.Proxy                              (Proxy (..))
import           Data.Text                               (Text)
import qualified Data.UUID                               as UUID
import           Ledger                                  (PubKey, Slot, Value)
import           Ledger.AddressMap                       (UtxoMap)
import           Ledger.Tx                               (Tx, TxOut (txOutValue), TxOutTx (txOutTxOut))
import           Plutus.PAB.Core                         (PABAction)
import qualified Plutus.PAB.Core                         as Core
import qualified Plutus.PAB.Effects.Contract             as Contract
import           Plutus.PAB.Events.Contract              (ContractPABRequest, _UserEndpointRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse (..))
import           Plutus.PAB.Types
import           Plutus.PAB.Webserver.Types
import           Servant                                 (NoContent (NoContent), (:<|>) ((:<|>)))
import           Servant.Client                          (ClientEnv, ClientM, runClientM)
import qualified Wallet.Effects                          as Wallet.Effects
import           Wallet.Emulator.Wallet                  (Wallet (..))
import           Wallet.Types                            (ContractInstanceId (..), NotificationError, Payment)

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
        byContractInstanceId rawInstanceId = contractSchema rawInstanceId :<|> undefined -- FIXME undefined

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

contractSchema :: forall t env. Contract.PABContract t => Text -> PABAction t env (ContractSignatureResponse (Contract.ContractDef t))
contractSchema = parseContractId @t @env >=> \contractId -> do
    def <- Contract.getDefinition @t contractId
    case def of
        Just ContractActivationArgs{caID} -> ContractSignatureResponse caID <$> Contract.exportSchema @t caID
        Nothing                           -> throwError (ContractInstanceNotFound contractId)

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
            :<|> (Text -> PABAction t env (ContractInstanceClientState)
                                        :<|> (String -> JSON.Value -> PABAction t env ()))
            :<|> (Integer -> PABAction t env [ContractInstanceClientState])
            :<|> PABAction t env [ContractInstanceClientState]
            :<|> PABAction t env [ContractSignatureResponse (Contract.ContractDef t)]
handlerNew =
        (activateContract
            -- :<|> (\x -> ((parseContractId @t @env x >>= contractInstanceState @t @env) :<|> (parseContractId @t @env x >>= callEndpoint @t @env)))
            :<|> (\x -> (parseContractId x >>= contractInstanceState) :<|> (\y z -> parseContractId x >>= \x' -> callEndpoint x' y z))
            :<|> instancesForWallets
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
callEndpoint a b v = Core.callEndpointOnInstance a b v >>= traverse_ (throwError @PABError . EndpointCallError)

instancesForWallets :: forall t env. Contract.PABContract t => Integer -> PABAction t env [ContractInstanceClientState]
instancesForWallets wallet = do
    mp <- Map.filter ((==) (Wallet wallet) . caWallet) <$> Contract.getActiveContracts @t
    let get i = fromInternalState i . Contract.serialisableState (Proxy @t) <$> Contract.getState @t i
    traverse get $ fst <$> Map.toList mp

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

-- | Proxy for the wallet API
walletProxyClientEnv ::
    forall t env.
    ClientEnv ->
    (PABAction t env Wallet -- Create new wallet
    :<|> (Integer -> Tx -> PABAction t env NoContent) -- Submit txn
    :<|> (Integer -> PABAction t env PubKey)
    :<|> (Integer -> (Value, Payment) -> PABAction t env Payment) -- Update payment with change
    :<|> (Integer -> PABAction t env Slot) -- Wallet slot
    :<|> (Integer -> PABAction t env UtxoMap)
    :<|> (Integer -> PABAction t env Value)
    :<|> (Integer -> Tx -> PABAction t env Tx))
walletProxyClientEnv clientEnv =
    let createWallet = runWalletClientM clientEnv Wallet.Client.createWallet
    in walletProxy createWallet

-- | Run a 'ClientM' action against a remote host using the given 'ClientEnv'.
runWalletClientM :: forall t env a. ClientEnv -> ClientM a -> PABAction t env a
runWalletClientM clientEnv action = do
    x <- sendM $ liftIO $ runClientM action clientEnv
    case x of
        Left err     -> throwError @PABError (WalletClientError err)
        Right result -> pure result

-- | Proxy for the wallet API
walletProxy ::
    forall t env.
    PABAction t env Wallet -> -- default action for creating a new wallet
    (PABAction t env Wallet -- Create new wallet
    :<|> (Integer -> Tx -> PABAction t env NoContent) -- Submit txn
    :<|> (Integer -> PABAction t env PubKey)
    :<|> (Integer -> (Value, Payment) -> PABAction t env Payment) -- Update payment with change
    :<|> (Integer -> PABAction t env Slot) -- Wallet slot
    :<|> (Integer -> PABAction t env UtxoMap)
    :<|> (Integer -> PABAction t env Value)
    :<|> (Integer -> Tx -> PABAction t env Tx))
walletProxy createNewWallet =
    ( createNewWallet
    :<|> (\w tx -> fmap (const NoContent) (Core.handleAgentThread (Wallet w) $ Wallet.Effects.submitTxn tx))
    :<|> (\w -> Core.handleAgentThread (Wallet w) Wallet.Effects.ownPubKey)
    :<|> (\w (value, payment) -> Core.handleAgentThread (Wallet w) $ Wallet.Effects.updatePaymentWithChange value payment)
    :<|> (\w -> Core.handleAgentThread (Wallet w) Wallet.Effects.walletSlot)
    :<|> (\w -> Core.handleAgentThread (Wallet w) Wallet.Effects.ownOutputs)
    :<|> (\w -> foldMap (txOutValue . txOutTxOut) <$> Core.handleAgentThread (Wallet w) Wallet.Effects.ownOutputs)
    :<|> (\w tx -> Core.handleAgentThread (Wallet w) $ Wallet.Effects.walletAddSignature tx)
    )

{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.Mock where

import           Cardano.Node.Follower           (NodeFollowerEffect, getBlocks, newFollower)
import           Cardano.Node.Types              (FollowerID)
import           Cardano.Wallet.Types            (WalletId)
import           Control.Lens                    (at, ix, makeLenses, non, to, view, (^.))
import           Control.Monad.Freer
import           Control.Monad.Freer.Error       (Error, runError, throwError)
import           Control.Monad.Freer.Extra.Log   (Log, logDebug, logInfo)
import           Control.Monad.Freer.Extra.State (assign, modifying, use)
import           Control.Monad.Freer.State       (State, gets)
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Data.Bifunctor                  (Bifunctor (..))
import qualified Data.ByteString.Lazy            as BSL
import qualified Data.ByteString.Lazy.Char8      as BSL8
import qualified Data.Map                        as Map
import           Data.Text.Encoding              (encodeUtf8)
import           Language.Plutus.Contract.Trace  (allWallets)
import           Ledger                          (Address, PubKey, TxOut (..), TxOutRef, TxOutTx (..), Value,
                                                  pubKeyAddress)
import           Ledger.AddressMap               (AddressMap, UtxoMap, addAddress)
import qualified Ledger.AddressMap               as AddressMap
import           Plutus.SCB.Arbitrary            ()
import           Plutus.SCB.Utils                (tshow)
import           Servant                         (NoContent (NoContent), ServerError, err401, err404, err500, errBody)
import           Test.QuickCheck                 (arbitrary, generate)
import           Wallet.API                      (WalletAPIError (InsufficientFunds, OtherError, PrivateKeyNotFound))
import           Wallet.Effects                  (NodeClientEffect, WalletEffect (..))
import qualified Wallet.Effects                  as W
import           Wallet.Emulator.Wallet          (Payment (..), PaymentArgs (..), Wallet (Wallet))
import qualified Wallet.Emulator.Wallet          as EM

data MockWalletState =
    MockWalletState
        { _watchedAddresses :: AddressMap
        , _followerID       :: Maybe FollowerID
        }
    deriving (Show, Eq)

makeLenses 'MockWalletState

handleWallet :: -- TODO: Merge with 'Wallet.Emulator.handleWallet'
                --       (the 'MockWalletState' and 'WalletState' types are
                --        different)
    ( Member (State MockWalletState) effs
    , Member NodeClientEffect effs
    , Member (Error WalletAPIError) effs
    )
    => Eff (WalletEffect ': effs) ~> Eff effs
handleWallet = interpret $ \case
    SubmitTxn tx -> W.publishTx tx
    OwnPubKey -> return (EM.walletPubKey activeWallet)
    UpdatePaymentWithChange vl (oldIns, changeOut) -> do
        utxo <- gets (view watchedAddresses)
        let pubK = EM.walletPubKey activeWallet
            args   = PaymentArgs
                        { availableFunds = utxo ^. AddressMap.fundsAt (pubKeyAddress pubK)
                        , ownPubKey = pubK
                        , requestedValue = vl
                        }
            pmt    = Payment{paymentInputs = oldIns, paymentChangeOutput = changeOut}
        Payment{paymentInputs, paymentChangeOutput} <- EM.handleUpdatePaymentWithChange args pmt
        pure (paymentInputs, paymentChangeOutput)
    WalletSlot -> W.getClientSlot
    OwnOutputs ->
        let address = pubKeyAddress (EM.walletPubKey activeWallet) in
        view (at address . non mempty) <$> gets (view watchedAddresses)

-- TODO Should this call syncstate itself?
initialState :: MockWalletState
initialState =
    MockWalletState
        { _watchedAddresses =
              foldr (addAddress . EM.walletAddress) mempty allWallets
        , _followerID = Nothing
        }

wallets :: (Member Log effs) => Eff effs [Wallet]
wallets = do
    logInfo "wallets"
    pure allWallets

fromWalletAPIError :: WalletAPIError -> ServerError
fromWalletAPIError (InsufficientFunds text) =
    err401 {errBody = BSL.fromStrict $ encodeUtf8 text}
fromWalletAPIError err@(PrivateKeyNotFound _) =
    err404 {errBody = BSL8.pack $ show err}
fromWalletAPIError (OtherError text) =
    err500 {errBody = BSL.fromStrict $ encodeUtf8 text}

valueAt ::
    ( Member Log effs
    , Member (State MockWalletState) effs
    )
    => Address
    -> Eff effs Value
valueAt address = do
    logInfo "valueAt"
    value <- use (watchedAddresses . to AddressMap.values . ix address)
    logInfo $ "valueAt " <> tshow address <> ": " <> tshow value
    pure value

selectCoin ::
    ( Member Log effs
    , Member (State MockWalletState) effs
    , Member (Error ServerError) effs
    )
    => WalletId
    -> Value
    -> Eff effs ([(TxOutRef, Value)], Value)
selectCoin walletId target = do
    logInfo "selectCoin"
    logInfo $ "  Wallet ID: " <> tshow walletId
    logInfo $ "     Target: " <> tshow target
    let address = EM.walletAddress (Wallet walletId)
    utxos :: UtxoMap <- use (watchedAddresses . AddressMap.fundsAt address)
    let funds :: [(TxOutRef, Value)]
        funds = fmap (second (txOutValue . txOutTxOut)) . Map.toList $ utxos
    result <- runM $ runError $ EM.selectCoin funds target
    logInfo $ "     Result: " <> tshow result
    case result of
        Right value -> pure value
        Left err    -> throwError $ fromWalletAPIError err

allocateAddress ::
    ( LastMember m effs
    , Member Log effs
    , MonadIO m
    )
    => WalletId
    -> Eff effs PubKey
allocateAddress _ = do
    logInfo "allocateAddress"
    sendM $ liftIO $ generate arbitrary

getOwnPubKey :: Member Log effs => Eff effs PubKey
getOwnPubKey = do
    logInfo "getOwnPubKey"
    pure $ EM.walletPubKey activeWallet

activeWallet :: Wallet
activeWallet = Wallet 1

getWatchedAddresses ::
    ( Member Log effs
    , Member (State MockWalletState) effs
    )
    => Eff effs AddressMap
getWatchedAddresses = do
    logInfo "getWatchedAddresses"
    use watchedAddresses

startWatching ::
    ( Member Log effs
    , Member (State MockWalletState) effs
    )
    => Address
    -> Eff effs NoContent
startWatching address = do
    logInfo "startWatching"
    modifying watchedAddresses (addAddress address)
    pure NoContent

------------------------------------------------------------
-- | Synchronise the initial state.
syncState ::
    ( Member Log effs
    , Member NodeFollowerEffect effs
    , Member (State MockWalletState) effs
    )
    => Eff effs ()
syncState = do
    logDebug "Synchronizing"
    fID <- getFollowerID
    blockchain <- getBlocks fID
    logDebug $ tshow fID <> " got " <> tshow (length blockchain) <> " blocks."
    modifying
        watchedAddresses
        (\m -> foldl (foldl (flip AddressMap.updateAllAddresses)) m blockchain)
    logDebug "Synchronized"

getFollowerID ::
    ( Member Log effs
    , Member NodeFollowerEffect effs
    , Member (State MockWalletState) effs
    )
    => Eff effs FollowerID
getFollowerID =
    use followerID >>= \case
        Just fID -> pure fID
        Nothing -> do
            logDebug "Subscribing"
            fID <- newFollower
            assign followerID (Just fID)
            pure fID

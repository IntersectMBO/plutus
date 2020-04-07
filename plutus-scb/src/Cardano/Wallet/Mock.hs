{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.Mock where

import           Cardano.Node.API               (NodeFollowerAPI (..))
import           Cardano.Node.Types             (FollowerID)
import           Cardano.Wallet.Types           (WalletId)
import           Control.Lens                   (assign, ix, makeLenses, modifying, to, use)
import           Control.Monad.Except           (MonadError, throwError)
import           Control.Monad.Freer            (runM)
import           Control.Monad.Freer.Error      (runError)
import           Control.Monad.IO.Class         (MonadIO, liftIO)
import           Control.Monad.Logger           (MonadLogger, logDebugN, logInfoN)
import           Control.Monad.State            (MonadState)
import           Data.Bifunctor                 (Bifunctor (..))
import qualified Data.ByteString.Lazy           as BSL
import qualified Data.ByteString.Lazy.Char8     as BSL8
import qualified Data.Map                       as Map
import           Data.Text.Encoding             (encodeUtf8)
import           Language.Plutus.Contract.Trace (allWallets)
import           Ledger                         (Address, PubKey, TxOut (..), TxOutRef, TxOutTx (..), Value)
import           Ledger.AddressMap              (AddressMap, UtxoMap, addAddress)
import qualified Ledger.AddressMap              as AddressMap
import           Plutus.SCB.Arbitrary           ()
import           Plutus.SCB.Utils               (tshow)
import           Servant                        (NoContent (NoContent), ServerError, err401, err404, err500, errBody)
import           Test.QuickCheck                (arbitrary, generate)
import           Wallet.API                     (WalletAPIError (InsufficientFunds, OtherError, PrivateKeyNotFound))
import           Wallet.Emulator.Wallet         (Wallet (Wallet))
import qualified Wallet.Emulator.Wallet         as EM

data State =
    State
        { _watchedAddresses :: AddressMap
        , _followerID       :: Maybe FollowerID
        }
    deriving (Show, Eq)

makeLenses 'State

-- TODO Should this call syncstate itself?
initialState :: State
initialState =
    State
        { _watchedAddresses =
              foldr (addAddress . EM.walletAddress) mempty allWallets
        , _followerID = Nothing
        }

wallets :: MonadLogger m => m [Wallet]
wallets = do
    logInfoN "wallets"
    pure allWallets

fromWalletAPIError :: WalletAPIError -> ServerError
fromWalletAPIError (InsufficientFunds text) =
    err401 {errBody = BSL.fromStrict $ encodeUtf8 text}
fromWalletAPIError err@(PrivateKeyNotFound _) =
    err404 {errBody = BSL8.pack $ show err}
fromWalletAPIError (OtherError text) =
    err500 {errBody = BSL.fromStrict $ encodeUtf8 text}

valueAt :: (MonadLogger m, MonadState State m) => Address -> m Value
valueAt address = do
    logInfoN "valueAt"
    value <- use (watchedAddresses . to AddressMap.values . ix address)
    logInfoN $ "valueAt " <> tshow address <> ": " <> tshow value
    pure value

selectCoin ::
       (MonadLogger m, MonadState State m, MonadError ServerError m)
    => WalletId
    -> Value
    -> m ([(TxOutRef, Value)], Value)
selectCoin walletId target = do
    logInfoN "selectCoin"
    logInfoN $ "  Wallet ID: " <> tshow walletId
    logInfoN $ "     Target: " <> tshow target
    let address = EM.walletAddress (Wallet walletId)
    utxos :: UtxoMap <- use (watchedAddresses . AddressMap.fundsAt address)
    let funds :: [(TxOutRef, Value)]
        funds = fmap (second (txOutValue . txOutTxOut)) . Map.toList $ utxos
    result <- runM $ runError $ EM.selectCoin funds target
    logInfoN $ "     Result: " <> tshow result
    case result of
        Right value -> pure value
        Left err    -> throwError $ fromWalletAPIError err

allocateAddress :: (MonadIO m, MonadLogger m) => WalletId -> m PubKey
allocateAddress _ = do
    logInfoN "allocateAddress"
    liftIO $ generate arbitrary

getOwnPubKey :: MonadLogger m => m PubKey
getOwnPubKey = do
    logInfoN "getOwnPubKey"
    pure $ EM.walletPubKey activeWallet

activeWallet :: Wallet
activeWallet = Wallet 1

getWatchedAddresses ::
       (MonadIO m, MonadLogger m, MonadState State m) => m AddressMap
getWatchedAddresses = do
    logInfoN "getWatchedAddresses"
    use watchedAddresses

startWatching ::
       (MonadIO m, MonadLogger m, MonadState State m) => Address -> m NoContent
startWatching address = do
    logInfoN "startWatching"
    modifying watchedAddresses (addAddress address)
    pure NoContent

------------------------------------------------------------
-- | Synchronise the initial state.
-- At the moment, this means, "as the node for UTXOs at all our watched addresses.
syncState :: (MonadLogger m, NodeFollowerAPI m, MonadState State m) => m ()
syncState = do
    logDebugN "Synchronizing"
    fID <- getFollowerID
    blockchain <- blocks fID
    logDebugN $ tshow fID <> " got " <> tshow (length blockchain) <> " blocks."
    modifying
        watchedAddresses
        (\m -> foldl (foldl (flip AddressMap.updateAllAddresses)) m blockchain)
    logDebugN "Synchronized"

getFollowerID ::
       (MonadLogger m, NodeFollowerAPI m, MonadState State m) => m FollowerID
getFollowerID =
    use followerID >>= \case
        Just fID -> pure fID
        Nothing -> do
            logDebugN "Subscribing"
            fID <- subscribe
            assign followerID (Just fID)
            pure fID

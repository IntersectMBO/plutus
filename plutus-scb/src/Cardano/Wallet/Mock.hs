{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Wallet.Mock where

import           Cardano.Wallet.Types           (WalletId)
import           Control.Lens                   (makeLenses, modifying, set, use)
import           Control.Monad.IO.Class         (MonadIO, liftIO)
import           Control.Monad.Logger           (MonadLogger, logInfoN)
import           Control.Monad.State            (MonadState, get, put)
import qualified Data.ByteString.Lazy           as BSL
import           Language.Plutus.Contract.Trace (allWallets)
import           Ledger                         (Address, Blockchain, PubKey, Signature, Value)
import           Ledger.AddressMap              (AddressMap, addAddress)
import qualified Ledger.AddressMap              as AddressMap
import qualified Ledger.Crypto                  as Crypto
import           Plutus.SCB.Arbitrary           ()
import           Plutus.SCB.Utils               (tshow)
import           Servant                        (NoContent (NoContent))
import           Servant.Client                 (ServantError)
import           Test.QuickCheck                (arbitrary, generate)
import           Wallet.Emulator.Wallet         (Wallet (Wallet))
import qualified Wallet.Emulator.Wallet         as EM

newtype State =
    State
        { _watchedAddresses :: AddressMap
        }
    deriving (Show, Eq)

makeLenses 'State

initialState :: State
initialState =
    State
        { _watchedAddresses =
              foldr (addAddress . EM.walletAddress) mempty allWallets
        }

wallets :: MonadLogger m => m [Wallet]
wallets = do
    logInfoN "wallets"
    pure allWallets

selectCoin :: MonadLogger m => WalletId -> Value -> m ([Value], Value)
selectCoin walletId target = do
    logInfoN "selectCoin"
    logInfoN $ "  Wallet ID: " <> tshow walletId
    logInfoN $ "     Target: " <> tshow target
    pure ([target], mempty)

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

sign :: MonadLogger m => BSL.ByteString -> m Signature
sign bs = do
    logInfoN "sign"
    let privK = EM.walletPrivKey activeWallet
    pure (Crypto.sign (BSL.toStrict bs) privK)

------------------------------------------------------------
-- | Synchronise the initial state.
-- At the moment, this means, "as the node for UTXOs at all our watched addresses.
syncState :: (MonadState State m) => m (Either ServantError Blockchain) -> m ()
syncState nodeClient = do
    oldState <- get
    result <- nodeClient
    case result of
        Left err -> error $ show err
        Right blockchain -> do
            let newAddressMap = AddressMap.fromChain blockchain
                newState = set watchedAddresses newAddressMap oldState
            put newState

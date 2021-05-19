module Capability.LocalStorage
  ( class ManageLocalStorage
  , getWalletLibrary
  , getCurrentWalletDetails
  , updateWalletDetails
  , addAssets
  , getContracts
  , insertContract
  , getAllWalletRoleContracts
  , getWalletRoleContracts
  , insertWalletRoleContracts
  ) where

import Prelude
import AppM (AppM)
import Control.Monad.Except (lift, runExcept)
import Data.Array (find)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Lens (set, view)
import Data.Map (Map, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Effect.Class (liftEffect)
import Foreign.Generic (decodeJSON, encodeJSON)
import Halogen (HalogenM)
import LocalStorage (getItem, setItem)
import Marlowe.PAB (MarloweParams, MarloweData)
import Marlowe.Semantics (Assets, TransactionInput)
import StaticData (contractsLocalStorageKey, walletDetailsLocalStorageKey, walletLibraryLocalStorageKey, walletRoleContractsLocalStorageKey)
import WalletData.Lenses (_assets, _companionAppId, _pubKeyHash, _walletInfo, _walletNickname)
import WalletData.Types (PubKeyHash, WalletLibrary, WalletDetails)

class
  Monad m <= ManageLocalStorage m where
  getWalletLibrary :: m WalletLibrary
  getCurrentWalletDetails :: m (Maybe WalletDetails)
  updateWalletDetails :: WalletDetails -> m Unit
  addAssets :: PubKeyHash -> Assets -> m Unit
  getContracts :: m (Map MarloweParams (Tuple MarloweData (Array TransactionInput)))
  insertContract :: MarloweParams -> (Tuple MarloweData (Array TransactionInput)) -> m Unit
  getAllWalletRoleContracts :: m (Map String (Map MarloweParams MarloweData))
  getWalletRoleContracts :: String -> m (Map MarloweParams MarloweData)
  insertWalletRoleContracts :: String -> MarloweParams -> MarloweData -> m Unit

instance manageLocalStorageAppM :: ManageLocalStorage AppM where
  getWalletLibrary = do
    mWalletLibraryJson <- liftEffect $ getItem walletLibraryLocalStorageKey
    pure
      $ case mWalletLibraryJson of
          Just json -> case runExcept $ decodeJSON json of
            Right wallets -> wallets
            Left _ -> mempty
          Nothing -> mempty
  getCurrentWalletDetails = do
    mWalletDetailsJson <- liftEffect $ getItem walletDetailsLocalStorageKey
    pure
      $ case mWalletDetailsJson of
          Just json -> case runExcept $ decodeJSON json of
            Right walletDetails -> Just walletDetails
            Left _ -> Nothing
          Nothing -> Nothing
  updateWalletDetails walletDetails = do
    walletLibrary <- getWalletLibrary
    let
      walletNickname = view _walletNickname walletDetails

      updatedWalletLibrary = insert walletNickname walletDetails walletLibrary
    void $ liftEffect $ setItem walletLibraryLocalStorageKey $ encodeJSON updatedWalletLibrary
    mCurrentWalletDetails <- getCurrentWalletDetails
    for_ mCurrentWalletDetails \currentDetails ->
      when (view _companionAppId currentDetails == view _companionAppId walletDetails)
        $ void
        $ liftEffect
        $ setItem walletDetailsLocalStorageKey
        $ encodeJSON walletDetails
  addAssets pubKeyHash assets = do
    walletLibrary <- getWalletLibrary
    for_ (find (\details -> view (_walletInfo <<< _pubKeyHash) details == pubKeyHash) walletLibrary) \details ->
      let
        existingAssets = view _assets details

        updatedAssets = existingAssets <> assets

        updatedDetails = set _assets updatedAssets details
      in
        updateWalletDetails updatedDetails
  getContracts = do
    mContractsJson <- liftEffect $ getItem contractsLocalStorageKey
    pure
      $ case mContractsJson of
          Just json -> case runExcept $ decodeJSON json of
            Right contracts -> contracts
            Left _ -> mempty
          Nothing -> mempty
  insertContract marloweParams contractData = do
    existingContracts <- getContracts
    let
      newContracts = insert marloweParams contractData existingContracts
    void $ liftEffect $ setItem contractsLocalStorageKey $ encodeJSON newContracts
  getAllWalletRoleContracts = do
    mAllWalletRoleContracts <- liftEffect $ getItem walletRoleContractsLocalStorageKey
    pure
      $ case mAllWalletRoleContracts of
          Just json -> case runExcept $ decodeJSON json of
            Right walletRoleContracts -> walletRoleContracts
            Left _ -> mempty
          Nothing -> mempty
  getWalletRoleContracts walletId = do
    allWalletRoleContracts <- getAllWalletRoleContracts
    case lookup walletId allWalletRoleContracts of
      Just roleContracts -> pure roleContracts
      Nothing -> pure mempty
  insertWalletRoleContracts walletId marloweParams marloweData = do
    allWalletRoleContracts <- getAllWalletRoleContracts
    walletRoleContracts <- getWalletRoleContracts walletId
    let
      newWalletRoleContracts = insert marloweParams marloweData walletRoleContracts

      newAllWalletRoleContracts = insert walletId newWalletRoleContracts allWalletRoleContracts
    void $ liftEffect $ setItem walletRoleContractsLocalStorageKey $ encodeJSON newAllWalletRoleContracts

instance manageLocalStorageHalogenM :: ManageLocalStorage m => ManageLocalStorage (HalogenM state action slots msg m) where
  getWalletLibrary = lift getWalletLibrary
  getCurrentWalletDetails = lift getCurrentWalletDetails
  updateWalletDetails = lift <<< updateWalletDetails
  addAssets walletDetails assets = lift $ addAssets walletDetails assets
  getContracts = lift getContracts
  insertContract marloweParams contractData = lift $ insertContract marloweParams contractData
  getAllWalletRoleContracts = lift getAllWalletRoleContracts
  getWalletRoleContracts = lift <<< getWalletRoleContracts
  insertWalletRoleContracts walletId marloweParams marloweData = lift $ insertWalletRoleContracts walletId marloweParams marloweData

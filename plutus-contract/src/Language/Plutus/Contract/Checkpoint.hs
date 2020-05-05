{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Checkpoint(
    -- * Checkpoints
    -- $checkpoints
    Checkpoint(..)
    , CheckpointError(..)
    , AsCheckpointError(..)
    , CheckpointStore(..)
    , CheckpointKey
    , jsonCheckpoint
    , handleCheckpoint
    ) where

import           Control.Lens
import           Control.Monad.Freer
import           Control.Monad.Freer.Error (Error, throwError)
import           Control.Monad.Freer.Log   (Log, logDebug)
import           Control.Monad.Freer.State (State, get, gets, modify, put)
import           Data.Aeson                (FromJSON, FromJSONKey, ToJSON, ToJSONKey, Value)
import qualified Data.Aeson.Types          as JSON
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Text                 (Text)
import qualified Data.Text                 as Text
import           Data.Text.Prettyprint.Doc (Pretty (..), colon, viaShow, vsep, (<+>))
import           GHC.Generics              (Generic)

-- $checkpoints
-- This module contains a checkpoints mechanism that can be used to store
-- intermediate results of 'Control.Monad.Freer.Eff' programs as JSON values
-- inside a 'CheckpointStore'. It works similar to the short-circuiting behavior
-- of 'Control.Monad.Freer.Error.Error': Before we execute an action
-- @Eff effs a@ whose result should be checkpointed, we check if the there is
-- already a value of @a@ for this checkpoint it in the store. If there is, we
-- return it /instead/ of running the action. If there isn't, we run the action
-- @a@ and then store the result.
--
-- * To create a checkpoint use 'jsonCheckpoint'.
-- * To handle the checkpoint effect use 'handleCheckpoint'.


newtype CheckpointKey = CheckpointKey Integer
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (FromJSON, ToJSON, ToJSONKey, FromJSONKey, Num, Enum, Pretty)

data CheckpointError = JSONDecodeError Text
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

makeClassyPrisms ''CheckpointError

newtype CheckpointStore = CheckpointStore { unCheckpointStore :: Map CheckpointKey Value }
    deriving stock (Eq, Show, Generic)
    deriving newtype (ToJSON, FromJSON, Semigroup, Monoid)

instance Pretty CheckpointStore where
    pretty (CheckpointStore mp) =
        let p k v = pretty k <> colon <+> viaShow v in
        vsep (uncurry p <$> Map.toList mp)

_CheckpointStore :: Iso' CheckpointStore (Map CheckpointKey Value)
_CheckpointStore = iso unCheckpointStore CheckpointStore

data CheckpointStoreItem a =
    CheckpointStoreItem
        { csValue  :: a
        , csNewKey :: CheckpointKey
        }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

{-| Insert a new value into the checkpoint store. The first 'CheckpointKey' is
    the checkpoint key *before* running the checkpointed action, the second
    'Checkpoint' key is the value *after* running it. When we restore the
    checkpoint from the state (in 'restore') we set the 'CheckpointKey' state
    to the second argument to prevent chaos.
-}
insert ::
    ( ToJSON a
    , Member (State CheckpointStore) effs
    )
    => CheckpointKey
    -> CheckpointKey
    -> a
    -> Eff effs ()
insert k k' v =
    let vl = CheckpointStoreItem{csValue = v, csNewKey = k'}
    in modify (over _CheckpointStore (Map.insert k (JSON.toJSON vl)))

{-| @restore k@ checks for an entry for @k@ in the checkpoint store,
    and parses the result if there is such an entry. It returns

    * @Right Nothing@ if no entry was found
    * @Left err@ if an entry was found but failed to parse with the
      'FromJSON' instance
    * @Right (Just a)@ if an entry was found and parsed succesfully.

-}
restore ::
    forall a effs.
    ( FromJSON a
    , Member (State CheckpointStore) effs
    , Member (State CheckpointKey) effs
    , Member Log effs
    )
    => CheckpointKey
    -> Eff effs (Either CheckpointError (Maybe a))
restore k = do
    value <- gets (view $ _CheckpointStore . at k)
    let (result :: Maybe (Either String (CheckpointStoreItem a))) = fmap (JSON.parseEither JSON.parseJSON) value
    case result of
        Nothing -> do
            logDebug $ "No value for " <> Text.pack (show k)
            pure $ Right Nothing
        Just (Left err) -> do
            logDebug $ "Decoding error at key " <> Text.pack (show k)
            pure $ Left (JSONDecodeError $ Text.pack err)
        Just (Right CheckpointStoreItem{csValue,csNewKey}) -> do
            logDebug "Found a value, restoring previous key"
            put csNewKey
            pure (Right (Just csValue))

data Checkpoint r where
    DoCheckpoint :: Checkpoint ()
    AllocateKey :: Checkpoint CheckpointKey
    Store :: (ToJSON a) => CheckpointKey -> CheckpointKey -> a -> Checkpoint ()
    Retrieve :: (FromJSON a) => CheckpointKey -> Checkpoint (Either CheckpointError (Maybe a))

doCheckpoint :: forall effs. Member Checkpoint effs => Eff effs ()
doCheckpoint = send DoCheckpoint

allocateKey :: forall effs. Member Checkpoint effs => Eff effs CheckpointKey
allocateKey = send AllocateKey

store :: forall a effs. (Member Checkpoint effs, ToJSON a) => CheckpointKey -> CheckpointKey -> a -> Eff effs ()
store k1 k2 a = send @Checkpoint (Store k1 k2 a)

retrieve :: forall a effs. (Member Checkpoint effs, FromJSON a) => CheckpointKey -> Eff effs (Either CheckpointError (Maybe a))
retrieve k = send @Checkpoint (Retrieve k)

-- | Handle the 'Checkpoint' effect in terms of 'CheckpointStore' and
--   'CheckpointKey' states.
handleCheckpoint ::
    forall effs.
    ( Member (State CheckpointStore) effs
    , Member (State CheckpointKey) effs
    , Member Log effs
    )
    => Eff (Checkpoint ': effs)
    ~> Eff effs
handleCheckpoint = interpret $ \case
    DoCheckpoint -> do
        logDebug "handleCheckpoint: doCheckpoint"
        modify @CheckpointKey succ
    AllocateKey -> do
        logDebug "handleCheckpoint: allocateKey"
        get @CheckpointKey
    Store k k' a -> do
        logDebug "handleCheckpoint: store"
        logDebug $ "key1: " <> Text.pack (show k)
        logDebug $ "key2: " <> Text.pack (show k')
        insert k k' a
    Retrieve k -> do
        logDebug "handleCheckpoint: retrieve"
        logDebug $ "key then: " <> Text.pack (show k)
        result <- restore @_ @effs k
        k' <- get @CheckpointKey
        logDebug $ "key now: " <> Text.pack (show k')
        pure result

{-| Create a checkpoint for an action.
    @handleCheckpoint (jsonCheckpoint action)@ will

    * Obtain a 'CheckpointKey' that identifies the position of the current
      checkpoint in the program
    * Run @action@, convert its result to JSON and store it in the checkpoint
      store if there is no value at the key
    * Retrieve the result as a JSON value from the store, parse it, and return
      it *instead* of running @action@ if there is a value at the key.

-}
jsonCheckpoint ::
    forall err a effs.
    ( Member Checkpoint effs
    , Member (Error err) effs
    , ToJSON a
    , FromJSON a
    , AsCheckpointError err
    )
    => Eff effs a -- ^ The @action@ that is checkpointed
    -> Eff effs a
jsonCheckpoint action = do
    doCheckpoint
    k <- allocateKey
    vl <- retrieve @_ k
    case vl of
        Left err -> throwError @err (review _CheckpointError err)
        Right (Just a) -> return a
        Right Nothing -> do
            result <- action
            k' <- allocateKey
            store  @_ k k' result
            pure result

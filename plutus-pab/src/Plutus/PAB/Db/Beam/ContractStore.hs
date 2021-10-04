{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

{-

'beam' handler for the 'ContractStore' effect

-}
module Plutus.PAB.Db.Beam.ContractStore
  (handleContractStore)
  where

import           Control.Lens
import           Control.Monad                       (join)
import           Control.Monad.Freer                 (Eff, Member, type (~>))
import           Control.Monad.Freer.Error           (Error, throwError)
import           Control.Monad.Freer.Extras          (LogMsg)
import           Control.Monad.Freer.Extras.Beam     (BeamEffect (..), addRows, selectList, selectOne, updateRows)
import           Data.Aeson                          (FromJSON, ToJSON, decode, encode)
import           Data.ByteString.Builder             (toLazyByteString)
import qualified Data.ByteString.Char8               as B
import qualified Data.ByteString.Lazy.Char8          as LB
import           Data.Map                            (Map)
import qualified Data.Map                            as Map
import           Data.Maybe                          (fromMaybe)
import           Data.Text                           (Text)
import qualified Data.Text                           as Text
import           Data.Text.Encoding                  (encodeUtf8Builder)
import qualified Data.Text.Encoding                  as Text
import           Data.Typeable                       (Proxy (..), typeRep)
import           Data.UUID                           (fromText, toText)
import           Database.Beam
import           Plutus.PAB.Db.Schema                hiding (ContractInstanceId)
import           Plutus.PAB.Effects.Contract         (ContractStore (..), PABContract (..))
import           Plutus.PAB.Effects.Contract.Builtin (Builtin, HasDefinitions (getContract), fromResponse, getResponse)
import           Plutus.PAB.Monitoring.Monitoring    (PABMultiAgentMsg)
import           Plutus.PAB.Types                    (PABError (..))
import           Plutus.PAB.Webserver.Types          (ContractActivationArgs (..))
import           Wallet.Emulator.Wallet              (Wallet (..))
import qualified Wallet.Emulator.Wallet              as Wallet
import           Wallet.Types                        (ContractActivityStatus (..), ContractInstanceId (..))

-- | Convert from the internal representation of a contract into the database
-- representation.
mkRow
  :: (ToJSON a)
  => ContractActivationArgs (ContractDef (Builtin a))
  -> ContractInstanceId
  -> ContractInstance
mkRow ContractActivationArgs{caID, caWallet} instanceId
  = ContractInstance
      (uuidStr instanceId)
      (Text.decodeUtf8 $ B.concat $ LB.toChunks $ encode caID)
      (Wallet.toBase16 . getWalletId . fromMaybe (Wallet.knownWallet 1) $ caWallet)
      Nothing -- No state, initially
      True    -- 'Active' immediately

-- | Convert from the database representation of a contract into the
-- internal representation.
mkContracts
  :: forall a.
  ( FromJSON a )
  => [ContractInstance]
  -> Map ContractInstanceId (ContractActivationArgs (ContractDef (Builtin a)))
mkContracts xs =
  Map.fromList xs'
    where
      -- Silently drop those items that failed to decode to UUIDs and contract id
      xs'    = [ (k, v) | Just (k, v) <- map f xs ]
      toId i = ContractInstanceId <$> fromText i
      f ci   = do
          ciId <- toId $ _contractInstanceId ci
          contractId <- decode
                      . toLazyByteString
                      . encodeUtf8Builder
                      . _contractInstanceContractId
                      $ ci
          wallet <- fmap Wallet . either (const Nothing) Just . Wallet.fromBase16 . _contractInstanceWallet $ ci
          return ( ciId
                 , ContractActivationArgs contractId (Just wallet)
                 )

-- | Our database doesn't store UUIDs natively, so we need to convert them
-- from a string.
uuidStr :: ContractInstanceId -> Text
uuidStr = toText . unContractInstanceId

-- | Run the 'ContractStore' actions against the database.
handleContractStore ::
  forall a effs.
  ( Member BeamEffect effs
  , Member (Error PABError) effs
  , Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
  , ToJSON a
  , FromJSON a
  , HasDefinitions a
  , Typeable a
  )
  => ContractStore (Builtin a)
  ~> Eff effs
handleContractStore = \case
  PutStartInstance args instanceId ->
    addRows
      $ insert (_contractInstances db)
      $ insertValues [ mkRow args instanceId ]

  PutState _ instanceId state ->
    let encode' = Text.decodeUtf8 . B.concat . LB.toChunks . encode . getResponse
    in do
        updateRows
          $ update (_contractInstances db)
              (\ci -> ci ^. contractInstanceState <-. val_ (Just $ encode' state))
              (\ci -> ci ^. contractInstanceId ==. val_ (uuidStr instanceId))

  GetState instanceId -> do
    let decodeText = decode . toLazyByteString . encodeUtf8Builder
        extractState = \case
          Nothing -> throwError $ ContractInstanceNotFound instanceId
          Just  c ->
            do
              let a = _contractInstanceContractId c
                  ty = Text.pack $ show $ typeRep (Proxy :: Proxy a)

              caID <- maybe (throwError $ AesonDecodingError ("Couldn't JSON decode this as Type `a`: " <> ty) a)
                        pure
                        (decode . toLazyByteString . encodeUtf8Builder $ a)

              resp <- maybe (throwError $ ContractStateNotFound instanceId)
                        pure
                        (_contractInstanceState c >>= decodeText)

              let cd = getContract @a caID
              fromResponse @a instanceId cd resp

    join
      $ fmap extractState
      $ selectOne
      $ select
      $ do
          inst <- all_ (_contractInstances db)
          guard_ (inst ^. contractInstanceId ==. val_ (uuidStr instanceId))
          pure inst

  PutStopInstance instanceId ->
    updateRows
      $ update (_contractInstances db)
          (\ci -> ci ^. contractInstanceActive <-. val_ False)
          (\ci -> ci ^. contractInstanceId ==. val_ (uuidStr instanceId))

  GetContracts mStatus ->
    fmap mkContracts
      $ selectList
      $ select
      $ do
          ci <- all_ (_contractInstances db)
          case mStatus of
            Just s -> guard_ ( ci ^. contractInstanceActive ==. val_ (s == Active) )
            _      -> pure ()
          pure ci

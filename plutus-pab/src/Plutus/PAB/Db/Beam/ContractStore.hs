{-# LANGUAGE DeriveAnyClass    #-}
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
import           Control.Monad                           (join)
import           Control.Monad.Freer                     (Eff, Member, type (~>))
import           Control.Monad.Freer.Error               (Error, throwError)
import           Data.Aeson                              (decode, encode)
import           Data.ByteString.Builder                 (toLazyByteString)
import qualified Data.ByteString.Char8                   as B
import qualified Data.ByteString.Lazy.Char8              as LB
import           Data.Map                                (Map)
import qualified Data.Map                                as Map
import           Data.Maybe                              (fromMaybe)
import           Data.Text                               (Text)
import qualified Data.Text                               as Text
import           Data.Text.Encoding                      (encodeUtf8Builder)
import qualified Data.Text.Encoding                      as Text
import           Data.UUID                               (fromText, toText)
import           Database.Beam                           hiding (updateRow)
import           Plutus.PAB.Effects.Contract             (ContractStore (..), PABContract (..))
import           Plutus.PAB.Effects.Contract.ContractExe (ContractExe (..))
import           Plutus.PAB.Effects.DbStore              hiding (ContractInstanceId, contractPath)
import           Plutus.PAB.Types                        (PABError (..))
import           Plutus.PAB.Webserver.Types              (ContractActivationArgs (..))
import           Wallet.Emulator.Wallet                  (Wallet (..))
import           Wallet.Types                            (ContractInstanceId (..))

mkRow
  :: ContractActivationArgs (ContractDef ContractExe)
  -> ContractInstanceId
  -> ContractInstance
mkRow (ContractActivationArgs{caID, caWallet}) instanceId
  = ContractInstance
      (uuidStr instanceId)
      (Text.pack $ contractPath caID)
      (Text.pack . show . getWallet $ caWallet)
      Nothing -- No state, initially
      True    -- 'Active' immediately

mkContracts
  :: [ContractInstance]
  -> Map ContractInstanceId (ContractActivationArgs (ContractDef ContractExe))
mkContracts xs =
  Map.fromList xs'
    where
      -- Silently drop those items that failed to decode to UUIDs (shouldn't
      -- ever happen ....)
      xs'    = [ (k, v) | (Just k, v) <- map f xs ]
      toId i = ContractInstanceId <$> fromText i
      f ci   = ( toId . _contractInstanceId $ ci
               , ContractActivationArgs
                   (ContractExe . Text.unpack . _contractInstanceContractPath $ ci)
                   (Wallet . read . Text.unpack . _contractInstanceWallet $ ci)
               )

uuidStr :: ContractInstanceId -> Text
uuidStr = toText . unContractInstanceId

handleContractStore ::
  forall effs.
  ( Member DbStoreEffect effs
  , Member (Error PABError) effs
  )
  => ContractStore ContractExe
  ~> Eff effs
handleContractStore = \case
  PutStartInstance args instanceId ->
    addRow (_contractInstances db)
      $ mkRow args instanceId

  -- TODO: Should we use 'args' ?
  PutState _ instanceId state ->
    let encode' = Just . Text.decodeUtf8 . B.concat . LB.toChunks . encode
    in updateRow
        $ update (_contractInstances db)
            (\ci -> ci ^. contractInstanceState <-. val_ (encode' state))
            (\ci -> ci ^. contractInstanceId ==. val_ (uuidStr instanceId))

  GetState instanceId -> do
    let decodeText = decode . toLazyByteString . encodeUtf8Builder
        extractState = \case
          Nothing -> throwError $ ContractInstanceNotFound instanceId
          Just  c ->
            fromMaybe (throwError $ ContractStateNotFound instanceId)
                      (pure <$> (_contractInstanceState c >>= decodeText))

    join
      $ fmap extractState
      $ selectOne
      $ select
      $ do
          inst <- all_ (_contractInstances db)
          guard_ (inst ^. contractInstanceId ==. val_ (uuidStr instanceId))
          pure inst

  PutStopInstance instanceId ->
    updateRow
      $ update (_contractInstances db)
          (\ci -> ci ^. contractInstanceActive <-. val_ False)
          (\ci -> ci ^. contractInstanceId ==. val_ (uuidStr instanceId))

  GetActiveContracts ->
    fmap mkContracts
      $ selectList
      $ select
      $ do
          ci <- all_ (_contractInstances db)
          guard_ ( ci ^. contractInstanceActive ==. val_ True )
          pure ci

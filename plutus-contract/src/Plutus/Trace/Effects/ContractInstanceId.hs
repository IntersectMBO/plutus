{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-

An effect for generating fresh contract instance IDs.

-}
module Plutus.Trace.Effects.ContractInstanceId(
    ContractInstanceIdEff
    , nextId

    -- * Handlers
    , handleDeterministicIds
    , handleRandomIds
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH
import           Control.Monad.IO.Class    (MonadIO (..))
import           Data.Maybe                (fromMaybe, listToMaybe)
import           Wallet.Types              (ContractInstanceId (..), contractInstanceIDs, randomID)

data ContractInstanceIdEff r where
    NextId :: ContractInstanceIdEff ContractInstanceId
makeEffect ''ContractInstanceIdEff

-- | Handle 'ContractInstanceIdEff' using a random number generator
handleRandomIds ::
    (LastMember m effs, MonadIO m)
    => Eff (ContractInstanceIdEff ': effs)
    ~> Eff effs
handleRandomIds = interpretM $ \case
    NextId -> liftIO randomID

-- | Handle 'ContractInstanceIdEff' using the list of IDs
--   'contractInstanceIDs'.
handleDeterministicIds ::
    Eff (ContractInstanceIdEff ': effs)
    ~> Eff effs
handleDeterministicIds =
    evalState contractInstanceIDs
    . reinterpret @_ @(State [ContractInstanceId])
        (\case
            NextId -> do
                x <- gets (fromMaybe (error "handleDeterministicIds: ran out of IDs") . listToMaybe)
                modify @[ContractInstanceId] (drop 1)
                pure x)

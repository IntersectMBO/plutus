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

'beam' handler for the 'ContractDefinitionStore' effect

-}
module Plutus.PAB.Db.Beam.ContractDefinitionStore
  (handleContractDefinitionStore)
  where

import           Control.Monad.Freer                     (Eff, Member, type (~>))
import qualified Data.Text                               as Text
import           Database.Beam                           (all_, select)
import           Plutus.PAB.Effects.Contract             (ContractDefinitionStore (..))
import           Plutus.PAB.Effects.Contract.ContractExe (ContractExe (..))
import           Plutus.PAB.Effects.DbStore              hiding (contractPath)

mkRow :: ContractExe -> Contract
mkRow (ContractExe {contractPath}) = Contract (Text.pack contractPath)

fromRow :: Contract -> ContractExe
fromRow (Contract {_contractPath})  = ContractExe (Text.unpack _contractPath)

handleContractDefinitionStore ::
  forall effs.
  ( Member DbStoreEffect effs
  )
  => ContractDefinitionStore ContractExe
  ~> Eff effs
handleContractDefinitionStore = \case
  AddDefinition t -> addRow (_contracts db) (mkRow t)
  GetDefinitions  -> map fromRow <$> selectList (select (all_ (_contracts db)))

{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE StrictData           #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutus.PAB.Events.User where

import           Data.Aeson                  (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                (Generic)
import           Plutus.PAB.Effects.Contract (PABContract (..))

-- | Users can install contracts and transition them to a new state.
--   Contracts are identified by values of 't'.
newtype UserEvent t
    = InstallContract (ContractDef t)
    deriving stock Generic

deriving stock instance Show (ContractDef t) => Show (UserEvent t)
deriving stock instance Eq (ContractDef t) => Eq (UserEvent t)

deriving anyclass instance FromJSON (ContractDef t) => FromJSON (UserEvent t)
deriving anyclass instance ToJSON (ContractDef t) => ToJSON (UserEvent t)

instance Pretty (ContractDef t) => Pretty (UserEvent t) where
    pretty = \case
        InstallContract t -> "InstallContract:" <+> pretty t

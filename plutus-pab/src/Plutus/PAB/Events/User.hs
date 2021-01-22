{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StrictData         #-}

module Plutus.PAB.Events.User where

import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)

-- | Users can install contracts and transition them to a new state.
--   Contracts are identified by values of 't'.
newtype UserEvent t
    = InstallContract t
    deriving (Show, Eq, Generic)
    deriving newtype (FromJSON, ToJSON)

instance Pretty t => Pretty (UserEvent t) where
    pretty = \case
        InstallContract t -> "InstallContract:" <+> pretty t

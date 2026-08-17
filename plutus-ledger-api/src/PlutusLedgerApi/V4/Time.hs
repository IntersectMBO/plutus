{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusLedgerApi.V4.Time
  ( POSIXTime (..)
  , POSIXTimeRange (..)
  ) where

import PlutusTx.Prelude

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Time (POSIXTime (..))
import PlutusTx (makeIsDataSchemaIndexed)
import PlutusTx.Blueprint (HasBlueprintDefinition)
import PlutusTx.Blueprint.Definition.Derive (definitionRef)
import PlutusTx.Lift (makeLift)
import Prettyprinter (Pretty (pretty), comma, (<+>))
import Prelude qualified as Haskell

data POSIXTimeRange = POSIXTimeRange
  { fromInclusive :: Maybe POSIXTime
  -- ^ 'Nothing' means negative infinity.
  , untilExclusive :: Maybe POSIXTime
  -- ^ 'Nothing' means positive infinity.
  }
  deriving stock (Haskell.Eq, Haskell.Show, Generic)
  deriving anyclass (NFData, HasBlueprintDefinition)

instance Pretty POSIXTimeRange where
  pretty (POSIXTimeRange lo hi) = prettyFrom <+> comma <+> prettyUntil
    where
      prettyFrom = case lo of
        Nothing -> "(-Inf"
        Just t -> "[" <+> pretty t
      prettyUntil = case hi of
        Nothing -> "+Inf)"
        Just t -> pretty t <+> ")"

deriveEq ''POSIXTimeRange
$(makeIsDataSchemaIndexed ''POSIXTimeRange [('POSIXTimeRange, 0)])
$(makeLift ''POSIXTimeRange)

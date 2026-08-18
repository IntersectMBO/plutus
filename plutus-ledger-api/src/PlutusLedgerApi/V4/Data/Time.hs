{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusLedgerApi.V4.Data.Time
  ( POSIXTime (..)
  , POSIXTimeRange
  , pattern POSIXTimeRange
  , matchPOSIXTimeRange
  , fromInclusive
  , untilExclusive
  ) where

import PlutusTx.Prelude

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Data.Time (POSIXTime (..))
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint (ConstructorSchema (..), Schema (..))
import PlutusTx.Blueprint.Class (HasBlueprintSchema (schema))
import PlutusTx.Blueprint.Definition
  ( HasBlueprintDefinition (..)
  , HasSchemaDefinition
  , Unrolled
  , definitionIdFromType
  , definitionRef
  )
import PlutusTx.Blueprint.Definition.TF (Nub)
import PlutusTx.Blueprint.Schema.Annotation (SchemaInfo (..), emptySchemaInfo)
import PlutusTx.Lift (makeLift)
import Prettyprinter (Pretty (pretty), comma, (<+>))
import Prelude qualified as Haskell

PlutusTx.asData
  [d|
    data POSIXTimeRange = POSIXTimeRange
      { -- 'Nothing' means negative infinity.
        fromInclusive :: Haskell.Maybe POSIXTime
      , -- 'Nothing' means positive infinity.
        untilExclusive :: Haskell.Maybe POSIXTime
      }
      deriving stock (Haskell.Eq, Haskell.Show, Generic)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving anyclass (NFData)
    |]

instance HasBlueprintDefinition POSIXTimeRange where
  type
    Unroll POSIXTimeRange =
      Nub (POSIXTimeRange ': Unrolled (Haskell.Maybe POSIXTime))
  definitionId = definitionIdFromType @POSIXTimeRange

instance
  HasSchemaDefinition (Haskell.Maybe POSIXTime) referencedTypes
  => HasBlueprintSchema POSIXTimeRange referencedTypes
  where
  {-# INLINEABLE schema #-}
  schema =
    SchemaConstructor
      emptySchemaInfo {title = Haskell.Just "POSIXTimeRange"}
      ( MkConstructorSchema
          0
          [ definitionRef @(Haskell.Maybe POSIXTime) @referencedTypes
          , definitionRef @(Haskell.Maybe POSIXTime) @referencedTypes
          ]
      )

instance Pretty POSIXTimeRange where
  pretty (POSIXTimeRange lo hi) = prettyFrom <+> comma <+> prettyUntil
    where
      prettyFrom = case lo of
        Haskell.Nothing -> "(-Inf"
        Haskell.Just t -> "[" <+> pretty t
      prettyUntil = case hi of
        Haskell.Nothing -> "+Inf)"
        Haskell.Just t -> pretty t <+> ")"

deriveEq ''POSIXTimeRange
$(makeLift ''POSIXTimeRange)

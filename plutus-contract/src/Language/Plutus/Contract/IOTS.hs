{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE IncoherentInstances  #-}
{-# LANGUAGE OverloadedLabels     #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}
module Language.Plutus.Contract.IOTS(
    IotsType(..)
  , IotsRow(..)
  , rowSchema
  ) where

import           Data.Kind         (Type)
import           Data.Row
import           Data.Row.Internal
import           Data.Text         (Text)
import           Type.Reflection   (Typeable)

import           IOTS

class IotsExportable (HList (IotsRowTypes s)) => IotsRow (s :: Row *) where

  -- The list of types. Every @l :-> a@ in @s@ results in one
  -- @Tagged l (a -> ())@ in @IotsRowTypes s@.
  type IotsRowTypes s :: [Type]

  -- The 'IotsTypeRep' for the list of types
  -- mkRep :: IotsTypeRep (HList (IotsRowTypes s))
  mkRep :: HList (IotsRowTypes s)

instance IotsRow Empty where
  type IotsRowTypes Empty = '[]
  mkRep = HNil

instance (IotsRow (R bs), KnownSymbol l, IotsType a, Typeable a) => IotsRow (R (l :-> a ': bs)) where
  type IotsRowTypes (R (l :-> a ': bs)) = Tagged l (a -> ()) ': IotsRowTypes (R bs)
  mkRep =
    HCons (Tagged @l @(a -> ()) (const ())) (mkRep @(R bs))

-- | The IOTS schema for 's', calling @createEndpoint@ for each entry
--   in the row.
rowSchema :: forall s. IotsRow s => Text
rowSchema = export (mkRep @s)

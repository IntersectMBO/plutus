{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
module Language.PlutusTx.IsData.Class where

import           Data.ByteString               as BS

import           Prelude                       (Integer, Maybe (..))

import           Language.PlutusTx.Data

import           Language.PlutusTx.Functor
import           Language.PlutusTx.Traversable

import           Data.Kind
import           Data.Void

{-# ANN module "HLint: ignore" #-}

-- | A typeclass for types that can be converted to and from 'Data'.
class IsData (a :: Type) where
    toData :: a -> Data
    -- TODO: this should probably provide some kind of diagnostics
    fromData :: Data -> Maybe a

instance IsData Data where
    {-# INLINABLE toData #-}
    toData d = d
    {-# INLINABLE fromData #-}
    fromData d = Just d

instance IsData Integer where
    {-# INLINABLE toData #-}
    toData = I
    {-# INLINABLE fromData #-}
    fromData (I i) = Just i
    fromData _     = Nothing

instance IsData ByteString where
    {-# INLINABLE toData #-}
    toData b = B b
    {-# INLINABLE fromData #-}
    fromData (B b) = Just b
    fromData _     = Nothing

instance IsData a => IsData [a] where
    {-# INLINABLE toData #-}
    toData xs = List (fmap toData xs)
    {-# INLINABLE fromData #-}
    fromData (List ds) = traverse fromData ds
    fromData _         = Nothing

instance IsData Void where
    {-# INLINABLE toData #-}
    toData v = absurd v
    {-# INLINABLE fromData #-}
    fromData _ = Nothing

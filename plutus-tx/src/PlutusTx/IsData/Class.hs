{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
module PlutusTx.IsData.Class where

import           Data.ByteString      as BS

import           Prelude              (Integer, Maybe (..))

import           PlutusTx.Data

import           PlutusTx.Functor
import           PlutusTx.Traversable

import           Data.Kind
import           Data.Void

{-# ANN module "HLint: ignore" #-}

-- | A typeclass for types that can be converted to and from 'Data'.
class IsData (a :: Type) where
    toData :: a -> Data
    -- TODO: this should probably provide some kind of diagnostics
    fromData :: Data -> Maybe a

instance IsData Data where
    {-# NOINLINE toData #-}
    toData d = d
    {-# NOINLINE fromData #-}
    fromData d = Just d

instance IsData Integer where
    {-# NOINLINE toData #-}
    toData = I
    {-# NOINLINE fromData #-}
    fromData (I i) = Just i
    fromData _     = Nothing

instance IsData ByteString where
    {-# NOINLINE toData #-}
    toData b = B b
    {-# NOINLINE fromData #-}
    fromData (B b) = Just b
    fromData _     = Nothing

instance IsData a => IsData [a] where
    {-# NOINLINE toData #-}
    toData xs = List (fmap toData xs)
    {-# NOINLINE fromData #-}
    fromData (List ds) = traverse fromData ds
    fromData _         = Nothing

instance IsData Void where
    {-# NOINLINE toData #-}
    toData v = absurd v
    {-# NOINLINE fromData #-}
    fromData _ = Nothing

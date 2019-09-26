{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# OPTIONS_GHC -fno-strictness #-}
module Language.PlutusTx.IsData where

import           Data.ByteString.Lazy as BSL

import Prelude (Maybe(..), Either(..), Bool(..), Integer)

import Language.PlutusTx.Data
import Language.PlutusTx.Functor
import Language.PlutusTx.Applicative
import Language.PlutusTx.Eq

import Data.Kind

-- | A typeclass for types that can be converted to and from 'Data'.
class IsData (a :: Type) where
    toData :: a -> Data
    -- TODO: this should probably provide some kind of diagnostics
    fromData :: Data -> Maybe a

instance IsData Integer where
    {-# INLINABLE toData #-}
    toData = I
    {-# INLINABLE fromData #-}
    fromData (I i) = Just i
    fromData _     = Nothing

instance IsData ByteString where
    {-# INLINABLE toData #-}
    toData = B
    {-# INLINABLE fromData #-}
    fromData (B b) = Just b
    fromData _     = Nothing

instance IsData Bool where
    {-# INLINABLE toData #-}
    toData True = Constr 0 []
    toData False = Constr 1 []
    {-# INLINABLE fromData #-}
    fromData (Constr i [])
        | i == 0 = Just True
        | i == 1 = Just False
    fromData _     = Nothing

instance IsData () where
    {-# INLINABLE toData #-}
    toData _ = Constr 0 []
    {-# INLINABLE fromData #-}
    fromData (Constr i []) | i == 0 = Just ()
    fromData _             = Nothing

instance (IsData a, IsData b) => IsData (a, b) where
    {-# INLINABLE toData #-}
    toData (a, b) = Constr 0 [toData a, toData b]
    {-# INLINABLE fromData #-}
    fromData (Constr i [ad, bd]) | i == 0 = (,) <$> fromData @a ad <*> fromData @b bd
    fromData _                   = Nothing

instance IsData a => IsData (Maybe a) where
    {-# INLINABLE toData #-}
    toData (Just a) = Constr 0 [toData a]
    toData Nothing  = Constr 1 []
    {-# INLINABLE fromData #-}
    fromData (Constr i [ad]) | i == 0 = Just <$> fromData ad
    fromData (Constr i []) | i == 1 = Just Nothing
    fromData _               = Nothing

instance (IsData a, IsData b) => IsData (Either a b) where
    {-# INLINABLE toData #-}
    toData (Left a)  = Constr 0 [toData a]
    toData (Right b) = Constr 1 [toData b]
    {-# INLINABLE fromData #-}
    fromData (Constr i [ad]) | i == 0 = Left <$> fromData ad
    fromData (Constr i [bd]) | i == 1 = Left <$> fromData bd
    fromData _               = Nothing

-- TODO: maybe this should actually be encoded as a list!
instance IsData a => IsData [a] where
    {-# INLINABLE toData #-}
    toData [] = Constr 0 []
    toData (x:xs) = Constr 1 [toData x, toData xs]
    {-# INLINABLE fromData #-}
    fromData (Constr i []) | i == 0 = Just []
    fromData (Constr i [hd, td]) | i == 1 = (:) <$> fromData hd <*> fromData td
    fromData _             = Nothing

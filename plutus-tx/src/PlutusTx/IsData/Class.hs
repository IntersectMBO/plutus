{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.IsData.Class where

import           Prelude                    (Int, Integer, Maybe (..), error)

import qualified PlutusCore.Data            as PLC
import           PlutusTx.Builtins          as Builtins
import           PlutusTx.Builtins.Internal (BuiltinData (..))
import qualified PlutusTx.Builtins.Internal as BI

import           PlutusTx.Applicative
import           PlutusTx.Functor
import           PlutusTx.Trace

import           Data.Kind
import           Data.Void

import           GHC.TypeLits               (ErrorMessage (..), TypeError)


{- HLINT ignore -}

-- | A typeclass for types that can be converted to and from 'BuiltinData'.
class ToData (a :: Type) where
    -- | Convert a value to 'BuiltinData'.
    toBuiltinData :: a -> BuiltinData

class FromData (a :: Type) where
    -- TODO: this should probably provide some kind of diagnostics
    -- | Convert a value from 'BuiltinData', returning 'Nothing' if this fails.
    fromBuiltinData :: BuiltinData -> Maybe a

class UnsafeFromData (a :: Type) where
    -- | Convert a value from 'BuiltinData', calling 'error' if this fails.
    -- This is typically much faster than 'fromBuiltinData'.
    --
    -- When implementing this function, make sure to call 'unsafeFromBuiltinData'
    -- rather than 'fromBuiltinData' when converting substructures!
    unsafeFromBuiltinData :: BuiltinData -> a

instance ToData BuiltinData where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData = id
instance FromData BuiltinData where
    {-# INLINABLE fromBuiltinData #-}
    fromBuiltinData d = Just d
instance UnsafeFromData BuiltinData where
    {-# INLINABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData d = d

instance (TypeError ('Text "Int is not supported, use Integer instead"))
    => ToData Int where
    toBuiltinData = Prelude.error "unsupported"
instance (TypeError ('Text "Int is not supported, use Integer instead"))
    => FromData Int where
    fromBuiltinData = Prelude.error "unsupported"
instance (TypeError ('Text "Int is not supported, use Integer instead"))
    => UnsafeFromData Int where
    unsafeFromBuiltinData = Prelude.error "unsupported"

instance ToData Integer where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData i = mkI i
instance FromData Integer where
    {-# INLINABLE fromBuiltinData #-}
    fromBuiltinData d = matchData' d (\_ _ -> Nothing) (const Nothing) (const Nothing) (\i -> Just i) (const Nothing)
instance UnsafeFromData Integer where
    {-# INLINABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData = BI.unsafeDataAsI

instance ToData Builtins.BuiltinByteString where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData = mkB
instance FromData Builtins.BuiltinByteString where
    {-# INLINABLE fromBuiltinData #-}
    fromBuiltinData d = matchData' d (\_ _ -> Nothing) (const Nothing) (const Nothing) (const Nothing) (\b -> Just b)
instance UnsafeFromData Builtins.BuiltinByteString where
    {-# INLINABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData = BI.unsafeDataAsB

instance ToData a => ToData [a] where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData l = BI.mkList (mapToBuiltin l)
        where
          {-# INLINE mapToBuiltin #-}
          mapToBuiltin :: [a] -> BI.BuiltinList BI.BuiltinData
          mapToBuiltin = go
            where
                go :: [a] -> BI.BuiltinList BI.BuiltinData
                go []     = BI.mkNilData BI.unitval
                go (x:xs) = BI.mkCons (toBuiltinData x) (go xs)
instance FromData a => FromData [a] where
    {-# INLINABLE fromBuiltinData #-}
    fromBuiltinData d =
        matchData'
        d
        (\_ _ -> Nothing)
        (const Nothing)
        traverseFromBuiltin
        (const Nothing)
        (const Nothing)
        where
          {-# INLINE traverseFromBuiltin #-}
          traverseFromBuiltin :: BI.BuiltinList BI.BuiltinData -> Maybe [a]
          traverseFromBuiltin = go
            where
                go :: BI.BuiltinList BI.BuiltinData -> Maybe [a]
                go l = BI.chooseList l (const (pure [])) (\_ -> liftA2 (:) (fromBuiltinData (BI.head l)) (go (BI.tail l))) ()
instance UnsafeFromData a => UnsafeFromData [a] where
    {-# INLINABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData d = mapFromBuiltin (BI.unsafeDataAsList d)
        where
          {-# INLINE mapFromBuiltin #-}
          mapFromBuiltin :: BI.BuiltinList BI.BuiltinData -> [a]
          mapFromBuiltin = go
            where
                go :: BI.BuiltinList BI.BuiltinData -> [a]
                go l = BI.chooseList l (const []) (\_ -> unsafeFromBuiltinData (BI.head l) : go (BI.tail l)) ()

instance ToData Void where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData v = absurd v
instance FromData Void where
    {-# INLINABLE fromBuiltinData #-}
    fromBuiltinData _ = Nothing
instance UnsafeFromData Void where
    {-# INLINABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData _ = traceError "Pg" {-"unsafeFromBuiltinData: Void is not supported"-}

-- | Convert a value to 'PLC.Data'.
toData :: (ToData a) => a -> PLC.Data
toData a = builtinDataToData (toBuiltinData a)

-- | Convert a value from 'PLC.Data', returning 'Nothing' if this fails.
fromData :: (FromData a) => PLC.Data -> Maybe a
fromData d = fromBuiltinData (BuiltinData d)

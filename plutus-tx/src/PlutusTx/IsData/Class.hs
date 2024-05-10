-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.IsData.Class where

import Prelude qualified as Haskell (Either (..), Int, error)

import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Data qualified as PLC
import PlutusTx.Base
import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal (BuiltinData (..))
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Maybe (Maybe (..))

import PlutusTx.Applicative
import PlutusTx.ErrorCodes
import PlutusTx.Trace

import Data.Kind
import Data.Void

import GHC.TypeLits (ErrorMessage (..), TypeError)


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
    --
    -- This is a simple type without any validation, __use with caution__.
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
    => ToData Haskell.Int where
    toBuiltinData = Haskell.error "unsupported"
instance (TypeError ('Text "Int is not supported, use Integer instead"))
    => FromData Haskell.Int where
    fromBuiltinData = Haskell.error "unsupported"
instance (TypeError ('Text "Int is not supported, use Integer instead"))
    => UnsafeFromData Haskell.Int where
    unsafeFromBuiltinData = Haskell.error "unsupported"

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
    toBuiltinData = \case {}
instance FromData Void where
    {-# INLINABLE fromBuiltinData #-}
    fromBuiltinData _ = Nothing
instance UnsafeFromData Void where
    {-# INLINABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData _ = traceError voidIsNotSupportedError

{- | For the BLS12-381 G1 and G2 types we use the `compress` functions to convert
   to a ByteString and then encode that as Data as usual.  We have to be more
   careful going the other way because we decode a Data object to (possibly) get
   a BuiltinByteString and then uncompress the underlying ByteString to get a
   group element.  However uncompression can fail so we have to check what
   happens: we don't use bls12_381_G?_uncompress because that invokes `error` if
   something goes wrong (but we do use it for unsafeFromData).
-}
instance ToData Builtins.BuiltinBLS12_381_G1_Element where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData = toBuiltinData . Builtins.bls12_381_G1_compress
instance FromData Builtins.BuiltinBLS12_381_G1_Element where
    {-# INLINABLE fromBuiltinData #-}
    fromBuiltinData d =
        case fromBuiltinData d of
          Nothing -> Nothing
          Just (BI.BuiltinByteString bs) ->
              case BLS12_381.G1.uncompress bs of
                Haskell.Left _  -> Nothing
                Haskell.Right g -> Just $ toBuiltin g
instance UnsafeFromData Builtins.BuiltinBLS12_381_G1_Element where
    {-# INLINABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData = Builtins.bls12_381_G1_uncompress . unsafeFromBuiltinData

instance ToData Builtins.BuiltinBLS12_381_G2_Element where
    {-# INLINABLE toBuiltinData #-}
    toBuiltinData = toBuiltinData . Builtins.bls12_381_G2_compress
instance FromData Builtins.BuiltinBLS12_381_G2_Element where
    {-# INLINABLE fromBuiltinData #-}
    fromBuiltinData d =
        case fromBuiltinData d of
          Nothing -> Nothing
          Just (BI.BuiltinByteString bs) ->
              case BLS12_381.G2.uncompress bs of
                Haskell.Left _  -> Nothing
                Haskell.Right g -> Just $ toBuiltin g
instance UnsafeFromData Builtins.BuiltinBLS12_381_G2_Element where
    {-# INLINABLE unsafeFromBuiltinData #-}
    unsafeFromBuiltinData = Builtins.bls12_381_G2_uncompress . unsafeFromBuiltinData

{- | We do not provide instances of any of these classes for
   BuiltinBLS12_381_MlResult since there is no serialisation format: we expect
   that values of that type will only occur as the result of on-chain
   computations.
-}
instance (TypeError ('Text "toBuiltinData is not supported for BuiltinBLS12_381_MlResult"))
    => ToData Builtins.BuiltinBLS12_381_MlResult where
    toBuiltinData = Haskell.error "unsupported"
instance (TypeError ('Text "fromBuiltinData is not supported for BuiltinBLS12_381_MlResult"))
    => FromData Builtins.BuiltinBLS12_381_MlResult where
    fromBuiltinData = Haskell.error "unsupported"
instance (TypeError ('Text "unsafeFromBuiltinData is not supported for BuiltinBLS12_381_MlResult"))
    => UnsafeFromData Builtins.BuiltinBLS12_381_MlResult where
    unsafeFromBuiltinData = Haskell.error "unsupported"

-- | Convert a value to 'PLC.Data'.
toData :: (ToData a) => a -> PLC.Data
toData a = builtinDataToData (toBuiltinData a)

-- | Convert a value from 'PLC.Data', returning 'Nothing' if this fails.
fromData :: (FromData a) => PLC.Data -> Maybe a
fromData d = fromBuiltinData (BuiltinData d)

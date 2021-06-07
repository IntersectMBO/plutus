{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module JavaScript.TypedArray.Internal.Types where

import GHCJS.Types
import GHCJS.Internal.Types

import Data.Int
import Data.Typeable
import Data.Word

newtype SomeTypedArray (e :: TypedArrayElem) (m :: MutabilityType s) =
  SomeTypedArray JSVal deriving Typeable
instance IsJSVal (SomeTypedArray e m)

{-
newtype SomeSTTypedArray s e = SomeSTTypedArray JSVal
  deriving (Typeable)
-}

type SomeSTTypedArray s (e :: TypedArrayElem) = SomeTypedArray e (STMutable s)

-- -----------------------------------------------------------------------------

data TypedArrayElem = Int8Elem
                    | Int16Elem
                    | Int32Elem
                    | Uint8Elem
                    | Uint16Elem
                    | Uint32Elem
                    | Uint8ClampedElem
                    | Float32Elem
                    | Float64Elem

-- -----------------------------------------------------------------------------

type SomeInt8Array         = SomeTypedArray        Int8Elem
type SomeInt16Array        = SomeTypedArray        Int16Elem
type SomeInt32Array        = SomeTypedArray        Int32Elem

type SomeUint8Array        = SomeTypedArray        Uint8Elem
type SomeUint16Array       = SomeTypedArray        Uint16Elem
type SomeUint32Array       = SomeTypedArray        Uint32Elem

type SomeFloat32Array      = SomeTypedArray        Float32Elem
type SomeFloat64Array      = SomeTypedArray        Float64Elem

type SomeUint8ClampedArray = SomeTypedArray        Uint8ClampedElem

-- -----------------------------------------------------------------------------

type Int8Array             = SomeInt8Array         Immutable
type Int16Array            = SomeInt16Array        Immutable
type Int32Array            = SomeInt32Array        Immutable

type Uint8Array            = SomeUint8Array        Immutable
type Uint16Array           = SomeUint16Array       Immutable
type Uint32Array           = SomeUint32Array       Immutable

type Uint8ClampedArray     = SomeUint8ClampedArray Immutable

type Float32Array          = SomeFloat32Array      Immutable
type Float64Array          = SomeFloat64Array      Immutable

-- -----------------------------------------------------------------------------

type IOInt8Array           = SomeInt8Array         Mutable
type IOInt16Array          = SomeInt16Array        Mutable
type IOInt32Array          = SomeInt32Array        Mutable

type IOUint8Array          = SomeUint8Array        Mutable
type IOUint16Array         = SomeUint16Array       Mutable
type IOUint32Array         = SomeUint32Array       Mutable

type IOUint8ClampedArray   = SomeUint8ClampedArray Mutable

type IOFloat32Array        = SomeFloat32Array      Mutable
type IOFloat64Array        = SomeFloat64Array      Mutable

-- -----------------------------------------------------------------------------

type STInt8Array s         = SomeSTTypedArray s Int8Elem
type STInt16Array s        = SomeSTTypedArray s Int16Elem
type STInt32Array s        = SomeSTTypedArray s Int32Elem

type STUint8Array s        = SomeSTTypedArray s Uint8Elem
type STUint16Array s       = SomeSTTypedArray s Uint16Elem
type STUint32Array s       = SomeSTTypedArray s Uint32Elem

type STFloat32Array s      = SomeSTTypedArray s Float32Elem
type STFloat64Array s      = SomeSTTypedArray s Float64Elem

type STUint8ClampedArray s = SomeSTTypedArray s Uint8ClampedElem

-- -----------------------------------------------------------------------------

type family Elem x where
    Elem (SomeUint8Array m)        = Word8
    Elem (SomeUint8ClampedArray m) = Word8
    Elem (SomeUint16Array m)       = Word16
    Elem (SomeUint32Array m)       = Word
    Elem (SomeInt8Array m)         = Int8
    Elem (SomeInt16Array m)        = Int16
    Elem (SomeInt32Array m)        = Int
    Elem (SomeFloat32Array m)      = Double
    Elem (SomeFloat64Array m)      = Double
    
    Elem (STUint8Array s)          = Word8
    Elem (STUint8ClampedArray s)   = Word8
    Elem (STUint16Array s)         = Word16
    Elem (STUint32Array s)         = Word
    Elem (STInt8Array s)           = Int8
    Elem (STInt16Array s)          = Int16
    Elem (STInt32Array s)          = Int
    Elem (STFloat32Array s)        = Double
    Elem (STFloat64Array s)        = Double


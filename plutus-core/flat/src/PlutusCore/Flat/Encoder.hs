{-# LANGUAGE CPP                       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-- |Encoder and encoding primitives
module PlutusCore.Flat.Encoder (
    Encoding,
    (<>),
    NumBits,
    encodersS,
    mempty,
    strictEncoder,
    eTrueF,
    eFalseF,
    eFloat,
    eDouble,
    eInteger,
    eNatural,
    eWord16,
    eWord32,
    eWord64,
    eWord8,
    eBits,
    eBits16,
    eFiller,
    eBool,
    eTrue,
    eFalse,
    eBytes,
#if ! defined (ETA_VERSION)
    eUTF16,
#endif
    eLazyBytes,
    eShortBytes,
    eInt,
    eInt8,
    eInt16,
    eInt32,
    eInt64,
    eWord,
    eChar,
    encodeArrayWith,
    encodeListWith,
    Size,
    arrayBits,
    sWord,
    sWord8,
    sWord16,
    sWord32,
    sWord64,
    sInt,
    sInt8,
    sInt16,
    sInt32,
    sInt64,
    sNatural,
    sInteger,
    sFloat,
    sDouble,
    sChar,
    sBytes,
    sLazyBytes,
    sShortBytes,
    sUTF16,
    sFillerMax,
    sBool,
    sUTF8Max,
    eUTF8,
#ifdef ETA_VERSION
    trampolineEncoding,
#endif
    ) where

import PlutusCore.Flat.Encoder.Prim (eFalseF, eTrueF)
import PlutusCore.Flat.Encoder.Size (arrayBits)
import PlutusCore.Flat.Encoder.Strict
import PlutusCore.Flat.Encoder.Types (NumBits, Size)

#if ! MIN_VERSION_base(4,11,0)
import Data.Semigroup ((<>))
#endif

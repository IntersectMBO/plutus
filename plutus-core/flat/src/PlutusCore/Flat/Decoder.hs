{-# LANGUAGE CPP #-}
-- |Strict Decoder
module PlutusCore.Flat.Decoder (
    strictDecoder,
    listTDecoder,
    Decoded,
    DecodeException(..),
    Get,
    dByteString,
    dLazyByteString,
    dShortByteString,
    dShortByteString_,
#if! defined (ETA_VERSION)
    dUTF16,
#endif
    dUTF8,
    decodeArrayWith,
    decodeListWith,
    dFloat,
    dDouble,
    dInteger,
    dNatural,
    dChar,
    dBool,
    dWord8,
    dWord16,
    dWord32,
    dWord64,
    dWord,
    dInt8,
    dInt16,
    dInt32,
    dInt64,
    dInt,
    dBE8,
    dBE16,
    dBE32,
    dBE64,
    dBEBits8,
    dBEBits16,
    dBEBits32,
    dBEBits64,
    dropBits,

    ConsState(..),consOpen,consClose,consBool,consBits
    ) where

import PlutusCore.Flat.Decoder.Prim
import PlutusCore.Flat.Decoder.Run
import PlutusCore.Flat.Decoder.Strict
import PlutusCore.Flat.Decoder.Types

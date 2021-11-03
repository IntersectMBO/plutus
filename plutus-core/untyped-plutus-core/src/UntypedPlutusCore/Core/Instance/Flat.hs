{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module UntypedPlutusCore.Core.Instance.Flat where

import UntypedPlutusCore.Core.Type

import PlutusCore.Flat
import PlutusCore.Pretty

import Data.Word (Word8)
import Flat
import Flat.Decoder
import Flat.Decoder.Types
import Flat.Encoder
import Universe

import Data.Primitive (Ptr)
import Data.Proxy
import Foreign (minusPtr)
import GHC.TypeLits

{-
The definitions in this file rely on some Flat instances defined for typed plutus core.
You can find those in PlutusCore.Flat.
-}

{- Note [Stable encoding of PLC]
READ THIS BEFORE TOUCHING ANYTHING IN THIS FILE

We need the encoding of PLC on the blockchain to be *extremely* stable. It *must not* change
arbitrarily, otherwise we'll be unable to read back old transactions and validate them.

Consequently we don't use the derivable instances of `Flat` for the PLC types that go
on the chain.

However, the instances in this file *are* constrained by instances for names, type names,
and annotations. What's to stop the instances for *those* changing, thus changing
the overall encoding on the chain?

The answer is that what goes on the chain is *always* a `Program TyName Name ()`. The instances
for `TyName` and `Name` are nailed down here, and the instance for `()` is standard.

However, having this flexibility allows us to encode e.g. PLC with substantial annotations
(like position information) in situation where the stability is *not* critical, such as
for testing.
-}

{- Note [Encoding/decoding constructor tags using Flat]
Flat saves space when compared to CBOR by allowing tags to use the minimum
number of bits required for their encoding.

This requires specialised encode/decode functions for each constructor
that encodes a different number of possibilities. Here is a list of the
tags and their used/available encoding possibilities.

| Data type       | Function          | Used | Available |
|-----------------|-------------------|------|-----------|
| Terms           | encodeTerm        | 8    | 16        |

For format stability we are manually assigning the tag values to the
constructors (and we do not use a generic algorithm that may change this order).

All encodings use the function `safeEncodeBits :: NumBits -> Word8 -> Encoding`, which encodes
at most 8 bits of data, and the first argument specifies how many bits from the 8
available are actually used. This function also checks the size of the `Word8`
argument at runtime.

Flat uses an extra function in its class definition called `size`. Since we want
to reserve some space for future data constructors and we don't want to have the
sizes desynchronised from the encoding and decoding functions we have manual
implementations for them (if they have any constructors reserved for future use).

By default, Flat does not use any space to serialise `()`.
-}

{- Note [Deserialization size limits]
In order to prevent people encoding copyright or otherwise illegal data on the chain, we restrict the
amount of space which can be used for a leaf serialized node to 64 bytes, and we enforce this during
deserialization.

We do this by asking Flat how far through the input it is before and after parsing a constant. That way
we can tell generically how much data was used to parse a constant.
-}

-- | Using 4 bits to encode term tags.
termTagWidth :: NumBits
termTagWidth = 4

encodeTermTag :: Word8 -> Encoding
encodeTermTag = safeEncodeBits termTagWidth

decodeTermTag :: Get Word8
decodeTermTag = dBEBits8 termTagWidth

encodeTerm
    :: forall name uni fun ann
    . ( Closed uni
    , uni `Everywhere` Flat
    , PrettyPlc (Term name uni fun ann)
    , Flat fun
    , Flat ann
    , Flat name
    , Flat (Binder name)
    )
    => Term name uni fun ann
    -> Encoding
encodeTerm = \case
    Var      ann n    -> encodeTermTag 0 <> encode ann <> encode n
    Delay    ann t    -> encodeTermTag 1 <> encode ann <> encode t
    LamAbs   ann n t  -> encodeTermTag 2 <> encode ann <> encode (Binder n) <> encode t
    Apply    ann t t' -> encodeTermTag 3 <> encode ann <> encode t <> encode t'
    Constant ann c    -> encodeTermTag 4 <> encode ann <> encode c
    Force    ann t    -> encodeTermTag 5 <> encode ann <> encode t
    Error    ann      -> encodeTermTag 6 <> encode ann
    Builtin  ann bn   -> encodeTermTag 7 <> encode ann <> encode bn

data SizeLimit = NoLimit | Limit Integer

decodeTerm
    :: forall name uni fun ann
    . ( Closed uni
    , uni `Everywhere` Flat
    , PrettyPlc (Term name uni fun ann)
    , Flat fun
    , Flat ann
    , Flat name
    , Flat (Binder name)
    )
    => SizeLimit
    -> Get (Term name uni fun ann)
decodeTerm sizeLimit = go =<< decodeTermTag
    where go 0 = Var      <$> decode <*> decode
          go 1 = Delay    <$> decode <*> decode
          go 2 = LamAbs   <$> decode <*> (unBinder <$> decode) <*> decode
          go 3 = Apply    <$> decode <*> decode <*> decode
          go 4 = do
              ann <- decode

              -- See Note [Deserialization size limits]
              posPre <- getCurPtr
              con <- decode
              posPost <- getCurPtr
              let usedBytes = posPost `minusPtr` posPre

              let conNode :: Term name uni fun ann
                  conNode = Constant ann con
              case sizeLimit of
                  NoLimit -> pure conNode
                  Limit n ->
                      if fromIntegral usedBytes > n
                      then fail $ "Used more than " ++ show n ++ " bytes decoding the constant: " ++ show (prettyPlcDef conNode)
                      else pure conNode
            where
                -- Get the pointer where flat is currently decoding from. Requires digging into the innards of flat a bit.
                getCurPtr :: Get (Ptr Word8)
                getCurPtr = Get $ \_ s@S{currPtr} -> pure $ GetResult s currPtr
          go 5 = Force    <$> decode <*> decode
          go 6 = Error    <$> decode
          go 7 = Builtin  <$> decode <*> decode
          go t = fail $ "Unknown term constructor tag: " ++ show t

sizeTerm
    :: forall name uni fun ann
    . ( Closed uni
    , uni `Everywhere` Flat
    , PrettyPlc (Term name uni fun ann)
    , Flat fun
    , Flat ann
    , Flat name
    , Flat (Binder name)
    )
    => Term name uni fun ann
    -> NumBits
    -> NumBits
sizeTerm tm sz = termTagWidth + sz + case tm of
    Var      ann n    -> getSize ann + getSize n
    Delay    ann t    -> getSize ann + getSize t
    LamAbs   ann n t  -> getSize ann + getSize n + getSize t
    Apply    ann t t' -> getSize ann + getSize t + getSize t'
    Constant ann c    -> getSize ann + getSize c
    Force    ann t    -> getSize ann + getSize t
    Error    ann      -> getSize ann
    Builtin  ann bn   -> getSize ann + getSize bn

-- | A newtype to indicate that the program should be serialized with size checks
-- for constants.
newtype WithSizeLimits (n :: Nat) a = WithSizeLimits a

instance ( Closed uni
         , uni `Everywhere` Flat
         , PrettyPlc (Term name uni fun ann)
         , Flat fun
         , Flat ann
         , Flat name
         , Flat (Binder name)
         ) => Flat (Term name uni fun ann) where
    encode = encodeTerm
    decode = decodeTerm NoLimit
    size = sizeTerm

instance ( Closed uni
         , uni `Everywhere` Flat
         , PrettyPlc (Term name uni fun ann)
         , Flat fun
         , Flat ann
         , Flat name
         , Flat (Binder name)
         , KnownNat n
         ) => Flat (WithSizeLimits n (Term name uni fun ann)) where
    encode (WithSizeLimits t) = encodeTerm t
    decode = WithSizeLimits <$> decodeTerm (Limit $ natVal $ Proxy @n)
    size (WithSizeLimits t) = sizeTerm t

instance ( Closed uni
         , uni `Everywhere` Flat
         , PrettyPlc (Term name uni fun ann)
         , Flat fun
         , Flat ann
         , Flat name
         , Flat (Binder name)
         ) => Flat (Program name uni fun ann) where
    encode (Program ann v t) = encode ann <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode
    size (Program a v t) n = n + getSize a + getSize v + getSize t

instance ( Closed uni
         , uni `Everywhere` Flat
         , PrettyPlc (Term name uni fun ann)
         , Flat fun
         , Flat ann
         , Flat name
         , Flat (Binder name)
         , KnownNat n
         ) => Flat (WithSizeLimits n (Program name uni fun ann)) where
    encode (WithSizeLimits (Program ann v t)) = encode ann <> encode v <> encode (WithSizeLimits @n t)
    decode = do
        ann <- decode
        v <- decode
        (WithSizeLimits t) <- decode @(WithSizeLimits n (Term name uni fun ann))
        pure $ WithSizeLimits $ Program ann v t
    size (WithSizeLimits p) = size p

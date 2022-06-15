{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
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
import Flat.Encoder
import Universe

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
In order to prevent people encoding copyright or otherwise illegal data on the chain, we would like to
restrict the amount of data that can be controlled in an unrestricted fashion by the user. Fortunately,
most of the encoding does no allow much leeway for a user to control its content (when accounting for the
structure of the format itself). The main thing to worry about is bytestrings, but even there, the flat
encoding of bytestrings is a a sequence of 255-byte chunks. This is okay, since user-controlled data will
be broken up by the chunk metadata.
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
    Delay    ann t    -> encodeTermTag 1 <> encode ann <> encodeTerm t
    LamAbs   ann n t  -> encodeTermTag 2 <> encode ann <> encode (Binder n) <> encodeTerm t
    Apply    ann t t' -> encodeTermTag 3 <> encode ann <> encodeTerm t <> encodeTerm t'
    Constant ann c    -> encodeTermTag 4 <> encode ann <> encode c
    Force    ann t    -> encodeTermTag 5 <> encode ann <> encodeTerm t
    Error    ann      -> encodeTermTag 6 <> encode ann
    Builtin  ann bn   -> encodeTermTag 7 <> encode ann <> encode bn

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
    => (fun -> Bool)
    -> Get (Term name uni fun ann)
decodeTerm builtinPred = go
    where
        go = handleTerm =<< decodeTermTag
        handleTerm 0 = Var      <$> decode <*> decode
        handleTerm 1 = Delay    <$> decode <*> go
        handleTerm 2 = LamAbs   <$> decode <*> (unBinder <$> decode) <*> go
        handleTerm 3 = Apply    <$> decode <*> go <*> go
        handleTerm 4 = Constant <$> decode <*> decode
        handleTerm 5 = Force    <$> decode <*> go
        handleTerm 6 = Error    <$> decode
        handleTerm 7 = do
            ann <- decode
            fun <- decode
            let t :: Term name uni fun ann
                t = Builtin ann fun
            if builtinPred fun
            then pure t
            else fail $ "Forbidden builtin function: " ++ show (prettyPlcDef t)
        handleTerm t = fail $ "Unknown term constructor tag: " ++ show t

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

decodeProgram
    :: forall name uni fun ann
    . ( Closed uni
    , uni `Everywhere` Flat
    , PrettyPlc (Term name uni fun ann)
    , Flat fun
    , Flat ann
    , Flat name
    , Flat (Binder name)
    )
    => (fun -> Bool)
    -> Get (Program name uni fun ann)
decodeProgram builtinPred = Program <$> decode <*> decode <*> decodeTerm builtinPred

{- Note [Deserialization on the chain]
As discussed in Note [Deserialization size limits], we want to limit how big constants are when deserializing.
But the 'Flat' instances for plain terms and programs provided here don't do that: they implement unrestricted deserialization.

In practice we use a specialized decoder for the on-chain decoding which calls 'decodeProgram' directly.
Possibly we should remove these instances in future and only have instances for newtypes that clearly communicate
the expected behaviour.
-}

instance ( Closed uni
         , uni `Everywhere` Flat
         , PrettyPlc (Term name uni fun ann)
         , Flat fun
         , Flat ann
         , Flat name
         , Flat (Binder name)
         ) => Flat (Term name uni fun ann) where
    encode = encodeTerm
    decode = decodeTerm (const True)
    size = sizeTerm

-- This instance could probably be derived, but better to write it explicitly ourselves so we have control!
instance ( Closed uni
         , uni `Everywhere` Flat
         , PrettyPlc (Term name uni fun ann)
         , Flat fun
         , Flat ann
         , Flat name
         , Flat (Binder name)
         ) => Flat (Program name uni fun ann) where
    encode (Program ann v t) = encode ann <> encode v <> encode t

    size (Program a v t) n = n + getSize a + getSize v + getSize t

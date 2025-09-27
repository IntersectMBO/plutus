{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Flat instances for Plutus Core types. Make sure to read Note [Stable
-- encoding of TPLC] and Note [Stable encoding of UPLC] before touching anything
-- in this file.
module PlutusCore.FlatInstances
    ( safeEncodeBits
    ) where

import Codec.Extras.FlatViaSerialise
import PlutusCore.Core
import PlutusCore.Data (Data)
import PlutusCore.DeBruijn
import PlutusCore.Name.Unique

import Data.Proxy
import PlutusCore.Flat
import PlutusCore.Flat.Decoder
import PlutusCore.Flat.Encoder
import PlutusPrelude
import Universe

{- Note [Stable encoding of TPLC]
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

{- Note [Encoding/decoding TPLC constructor tags using Flat]
Flat saves space when compared to CBOR by allowing tags to use the minimum
number of bits required for their encoding.

This requires specialised encode/decode functions for each constructor
that encodes a different number of possibilities. Here is a list of the
tags and their used/available encoding possibilities.

** The BELOW table is about Typed-PLC and not UPLC. See `UntypedPlutusCore.Core.Instance.Flat`**

| Data type        | Function          | Bit Width | Total | Used | Remaining |
|------------------|-------------------|-----------|-------|------|-----------|
| default builtins | encodeBuiltin     | 7         | 128   | 54   | 74        |
| Kinds            | encodeKind        | 1         | 2     | 2    | 0         |
| Types            | encodeType        | 3         | 8     | 7    | 1         |
| Terms            | encodeTerm        | 4         | 16    | 12   | 4         |

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

{- Note [DeBruijn Index serialization]

Back in the days, `Index` was a Natural and we flat (de)-serialized it via Natural.
Later `Index` was changed to Word64 (for performance reasons):
its flat encoding remained via Natural,
but its decoding was changed to a *custom* Word64 decoder.

Why custom decoder: there was a bug in Word64 decoder of flat versions <0.5.2 and
fixed in flat>=0.5.2.

We are now running flat>=0.6, so we switch to the non-custom, fixed flat Word64 decoder.

Since we are there, we also switch the encoder of Index from the Natural encoder
to Word64 encoder. This encoding change only breaks client-code and not nodes' behavior:
the script would just fail earlier at encoding phase (in the client's software)
than the later decoding phase (when trying to send the encoded script to the node network and
only get back a decoding error, aka phase-1 validation error).
This phase-1 validation is in place both for normal (locked scripts) and for inline scripts,
so the nodes' behavior does not change.
-}

safeEncodeBits :: NumBits -> Word8 -> Encoding
safeEncodeBits maxBits v =
  if 2 ^ maxBits <= v
  then error $ "Overflow detected, cannot fit "
               <> show v <> " in " <> show maxBits <> " bits."
  else eBits maxBits v

constantWidth :: NumBits
constantWidth = 4

encodeConstant :: Word8 -> Encoding
encodeConstant = safeEncodeBits constantWidth

decodeConstant :: Get Word8
decodeConstant = dBEBits8 constantWidth

deriving via FlatViaSerialise Data instance Flat Data

decodeKindedUniFlat :: Closed uni => Get (SomeTypeIn (Kinded uni))
decodeKindedUniFlat =
    go . decodeKindedUni . map (fromIntegral :: Word8 -> Int)
        =<< decodeListWith decodeConstant
        where
        go Nothing    = fail "Failed to decode a universe"
        go (Just uni) = pure uni

-- See Note [The G, the Tag and the Auto].
instance Closed uni => Flat (SomeTypeIn uni) where
    encode (SomeTypeIn uni) =
      encodeListWith encodeConstant .
        map (fromIntegral :: Int -> Word8) $ encodeUni uni

    decode = decodeKindedUniFlat <&> \(SomeTypeIn (Kinded uni)) -> SomeTypeIn uni

    -- Encode a view of the universe, not the universe itself.
    size (SomeTypeIn uni) acc =
      acc +
      length (encodeUni uni) * (1 + constantWidth) + -- List Cons (1 bit) + constant
      1 -- List Nil (1 bit)

-- See Note [The G, the Tag and the Auto].
instance (Closed uni, uni `Everywhere` Flat) => Flat (Some (ValueOf uni)) where
    encode (Some (ValueOf uni x)) = encode (SomeTypeIn uni) <> bring (Proxy @Flat) uni (encode x)

    decode =
        decodeKindedUniFlat @uni >>= \(SomeTypeIn (Kinded uni)) ->
            -- See Note [Decoding universes].
            case checkStar uni of
                Nothing   -> fail "A non-star type can't have a value to decode"
                Just Refl -> Some . ValueOf uni <$> bring (Proxy @Flat) uni decode

    -- We need to get the flat instance in scope.
    size (Some (ValueOf uni x)) acc = size (SomeTypeIn uni) acc
                                        + bring (Proxy @Flat) uni (size x 0)

deriving newtype instance Flat Unique -- via int

instance Flat Name where
    encode (Name txt u) = encode txt <> encode u
    decode = Name <$> decode <*> decode

deriving newtype instance Flat TyName -- via Name

instance Flat Version where
    encode (Version n n' n'') = encode n <> encode n' <> encode n''
    decode = Version <$> decode <*> decode <*> decode

-- | Use 1 bit to encode kind tags.
kindTagWidth :: NumBits
kindTagWidth = 1

encodeKind :: Word8 -> Encoding
encodeKind = safeEncodeBits kindTagWidth

decodeKind :: Get Word8
decodeKind = dBEBits8 kindTagWidth

instance Flat ann => Flat (Kind ann) where
    encode = \case
        Type ann           -> encodeKind 0 <> encode ann
        KindArrow ann k k' -> encodeKind 1 <> encode ann <> encode k  <> encode k'

    decode = go =<< decodeKind
        where go 0 = Type      <$> decode
              go 1 = KindArrow <$> decode <*> decode <*> decode
              go _ = fail "Failed to decode Kind ()"

    size tm sz =
      let
        sz' = sz + kindTagWidth
      in case tm of
        Type ann           -> size ann sz'
        KindArrow ann k k' -> size ann $ size k $ size k' sz'

-- | Use 3 bits to encode type tags.
typeTagWidth :: NumBits
typeTagWidth = 3

encodeType :: Word8 -> Encoding
encodeType = safeEncodeBits typeTagWidth

decodeType :: Get Word8
decodeType = dBEBits8 typeTagWidth

instance (Closed uni, Flat ann, Flat tyname) => Flat (Type tyname uni ann) where
    encode = \case
        TyVar     ann tn      -> encodeType 0 <> encode ann <> encode tn
        TyFun     ann t t'    -> encodeType 1 <> encode ann <> encode t   <> encode t'
        TyIFix    ann pat arg -> encodeType 2 <> encode ann <> encode pat <> encode arg
        TyForall  ann tn k t  -> encodeType 3 <> encode ann <> encode tn  <> encode k <> encode t
        TyBuiltin ann con     -> encodeType 4 <> encode ann <> encode con
        TyLam     ann n k t   -> encodeType 5 <> encode ann <> encode n   <> encode k <> encode t
        TyApp     ann t t'    -> encodeType 6 <> encode ann <> encode t   <> encode t'
        -- Note that this relies on the instance for lists. We shouldn't use this in the
        -- serious on-chain version but it's okay here.
        TySOP    ann tyls     -> encodeType 7 <> encode ann <> encode tyls

    decode = go =<< decodeType
        where go 0 = TyVar     <$> decode <*> decode
              go 1 = TyFun     <$> decode <*> decode <*> decode
              go 2 = TyIFix    <$> decode <*> decode <*> decode
              go 3 = TyForall  <$> decode <*> decode <*> decode <*> decode
              go 4 = TyBuiltin <$> decode <*> decode
              go 5 = TyLam     <$> decode <*> decode <*> decode <*> decode
              go 6 = TyApp     <$> decode <*> decode <*> decode
              go 7 = TySOP     <$> decode <*> decode
              go _ = fail "Failed to decode Type TyName ()"

    size tm sz =
      let
        sz' = sz + typeTagWidth
      in case tm of
        TyVar     ann tn      -> size ann $ size tn sz'
        TyFun     ann t t'    -> size ann $ size t $ size t' sz'
        TyIFix    ann pat arg -> size ann $ size pat $ size arg sz'
        TyForall  ann tn k t  -> size ann $ size tn $ size k $ size t sz'
        TyBuiltin ann con     -> size ann $ size con sz'
        TyLam     ann n k t   -> size ann $ size n $ size k $ size t sz'
        TyApp     ann t t'    -> size ann $ size t $ size t' sz'
        TySOP     ann tyls    -> size ann $ size tyls sz'

termTagWidth :: NumBits
termTagWidth = 4

encodeTerm :: Word8 -> Encoding
encodeTerm = safeEncodeBits termTagWidth

decodeTerm :: Get Word8
decodeTerm = dBEBits8 termTagWidth

instance ( Closed uni
         , uni `Everywhere` Flat
         , Flat fun
         , Flat ann
         , Flat tyname
         , Flat name
         ) => Flat (Term tyname name uni fun ann) where
    encode = \case
        Var      ann n         -> encodeTerm 0 <> encode ann <> encode n
        TyAbs    ann tn k t    -> encodeTerm 1 <> encode ann <> encode tn  <> encode k   <> encode t
        LamAbs   ann n ty t    -> encodeTerm 2 <> encode ann <> encode n   <> encode ty  <> encode t
        Apply    ann t t'      -> encodeTerm 3 <> encode ann <> encode t   <> encode t'
        Constant ann c         -> encodeTerm 4 <> encode ann <> encode c
        TyInst   ann t ty      -> encodeTerm 5 <> encode ann <> encode t   <> encode ty
        Unwrap   ann t         -> encodeTerm 6 <> encode ann <> encode t
        IWrap    ann pat arg t -> encodeTerm 7 <> encode ann <> encode pat <> encode arg <> encode t
        Error    ann ty        -> encodeTerm 8 <> encode ann <> encode ty
        Builtin  ann bn        -> encodeTerm 9 <> encode ann <> encode bn
        Constr   ann ty i es   ->
          encodeTerm 10
          <> encode ann
          <> encode ty
          <> encode i
          <> encode es
        Case     ann ty arg cs ->
          encodeTerm 11
          <> encode ann
          <> encode ty
          <> encode arg
          <> encode cs

    decode = go =<< decodeTerm
        where go 0  = Var      <$> decode <*> decode
              go 1  = TyAbs    <$> decode <*> decode <*> decode <*> decode
              go 2  = LamAbs   <$> decode <*> decode <*> decode <*> decode
              go 3  = Apply    <$> decode <*> decode <*> decode
              go 4  = Constant <$> decode <*> decode
              go 5  = TyInst   <$> decode <*> decode <*> decode
              go 6  = Unwrap   <$> decode <*> decode
              go 7  = IWrap    <$> decode <*> decode <*> decode <*> decode
              go 8  = Error    <$> decode <*> decode
              go 9  = Builtin  <$> decode <*> decode
              go 10 = Constr   <$> decode <*> decode <*> decode <*> decode
              go 11 = Case     <$> decode <*> decode <*> decode <*> decode
              go _  = fail "Failed to decode Term TyName Name ()"

    size tm sz =
      let
        sz' = termTagWidth + sz
      in case tm of
        Var      ann n         -> size ann $ size n sz'
        TyAbs    ann tn k t    -> size ann $ size tn $ size k  $ size t sz'
        LamAbs   ann n ty t    -> size ann $ size n $ size ty $ size t sz'
        Apply    ann t t'      -> size ann $ size t $ size t' sz'
        Constant ann c         -> size ann $ size c sz'
        TyInst   ann t ty      -> size ann $ size t $ size ty sz'
        Unwrap   ann t         -> size ann $ size t sz'
        IWrap    ann pat arg t -> size ann $ size pat $ size arg $ size t sz'
        Error    ann ty        -> size ann $ size ty sz'
        Builtin  ann bn        -> size ann $ size bn sz'
        Constr   ann ty i es   -> size ann $ size ty $ size i $ size es sz'
        Case     ann ty arg cs -> size ann $ size ty $ size arg $ size cs sz'

instance ( Closed uni
         , Flat ann
         , Flat tyname
         , Flat name
         ) => Flat (VarDecl tyname name uni ann) where
    encode (VarDecl t name tyname ) = encode t <> encode name <> encode tyname
    decode = VarDecl <$> decode <*> decode <*> decode

instance (Flat ann, Flat tyname)  => Flat (TyVarDecl tyname ann) where
    encode (TyVarDecl t tyname kind) = encode t <> encode tyname <> encode kind
    decode = TyVarDecl <$> decode <*> decode <*> decode

instance ( Flat ann
         , Flat (Term tyname name uni fun ann)
         ) => Flat (Program tyname name uni fun ann) where
    encode (Program ann v t) = encode ann <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode

deriving newtype instance (Flat a) => Flat (Normalized a)

-- See Note [DeBruijn Index serialization]
deriving newtype instance Flat Index -- via word64

deriving newtype instance Flat DeBruijn -- via index
deriving newtype instance Flat TyDeBruijn -- via debruijn

instance Flat NamedDeBruijn where
    encode (NamedDeBruijn txt ix) = encode txt <> encode ix
    decode = NamedDeBruijn <$> decode <*> decode

deriving newtype instance Flat NamedTyDeBruijn -- via nameddebruijn

-- NOTE: the serialization roundtrip holds iff the invariant binder.index==0 holds
instance Flat (Binder DeBruijn) where
    size _ = id -- zero cost
    encode _ = mempty
    decode = pure $ Binder $ DeBruijn deBruijnInitIndex

-- (Binder TyDeBruijn) could similarly have a flat instance, but we don't need it.

deriving newtype instance Flat (Binder Name)
deriving newtype instance Flat (Binder TyName)
-- We could use an alternative, manual Flat-serialization of Named(Ty)DeBruijn
-- where we store the name only at the binder and the index only at the use-site (Var/TyVar).
-- That would be more compact, but we don't need it at the moment.
deriving newtype instance Flat (Binder NamedDeBruijn)
deriving newtype instance Flat (Binder NamedTyDeBruijn)

{- This instance is going via Flat DeBruijn.
FakeNamedDeBruijn <-> DeBruijn are isomorphic: we could use iso-deriving package,
but we do not need any other isomorphic Flat deriving for the moment.
See Note [Why newtype FakeNamedDeBruijn]
-}
instance Flat FakeNamedDeBruijn where
    size = size . fromFake
    encode = encode . fromFake
    decode =  toFake <$> decode

{- This instance is going via Flat (Binder DeBruijn) instance.
Binder FakeNamedDeBruijn <-> Binder DeBruijn are isomorphic because
FakeNamedDeBruijn <-> DeBruijn are isomorphic and Binder is a functor:
we could use iso-deriving package,
but  we do not need any other isomorphic Flat deriving for the moment.
See Note [Why newtype FakeNamedDeBruijn]
NOTE: the serialization roundtrip holds iff the invariant binder.index==0 holds
-}
instance Flat (Binder FakeNamedDeBruijn) where
    size = size . fmap fromFake
    encode = encode . fmap fromFake
    decode =  fmap toFake <$> decode

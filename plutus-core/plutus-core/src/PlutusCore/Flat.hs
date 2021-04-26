{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Flat instances for Plutus Core types. Make sure to read the
-- Note [Stable encoding of PLC] before touching anything in this
-- file.  Also see the Notes [Serialising unit annotations] and
-- [Serialising Scripts] before using anything in this file.

module PlutusCore.Flat ( encode
                                , decode
                                , safeEncodeBits
                                ) where

import           PlutusCore.Core
import           PlutusCore.DeBruijn
import           PlutusCore.Lexer.Type
import           PlutusCore.MkPlc      (TyVarDecl (..), VarDecl (..))
import           PlutusCore.Name
import           PlutusCore.Universe

import           Data.Proxy
import           Data.Word             (Word8)
import           Flat
import           Flat.Decoder
import           Flat.Encoder

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

| Data type        | Function          | Used | Available |
|------------------|-------------------|------|-----------|
| default builtins | encodeBuiltin     | 22   | 32        |
| Kinds            | encodeKind        | 2    | 2         |
| Types            | encodeType        | 7    | 8         |
| BuiltinNames     | encodeBuiltinName | 2    | 2         |
| Terms            | encodeTerm        | 10   | 16        |

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

safeEncodeBits :: NumBits -> Word8 -> Encoding
safeEncodeBits n v =
  if 2 ^ n < v
  then error $ "Overflow detected, cannot fit "
               <> show v <> " in " <> show n <> " bits."
  else eBits n v

constantWidth :: NumBits
constantWidth = 4

encodeConstant :: Word8 -> Encoding
encodeConstant = safeEncodeBits constantWidth

decodeConstant :: Get Word8
decodeConstant = dBEBits8 constantWidth

-- See Note [The G, the Tag and the Auto].
instance Closed uni => Flat (Some (TypeIn uni)) where
    encode (Some (TypeIn uni)) =
      encodeListWith encodeConstant .
        map (fromIntegral :: Int -> Word8) $ encodeUni uni

    decode = go . decodeUni . map (fromIntegral :: Word8 -> Int)
                =<< decodeListWith decodeConstant
        where
        go Nothing    = fail "Failed to decode a universe"
        go (Just uni) = pure uni

    -- Encode a view of the universe, not the universe itself.
    size (Some (TypeIn uni)) acc =
      acc +
      length (encodeUni uni) * (1 + constantWidth) + -- List Cons (1 bit) + constant
      1 -- List Nil (1 bit)

-- See Note [The G, the Tag and the Auto].
instance (Closed uni, uni `Everywhere` Flat) => Flat (Some (ValueOf uni)) where
    encode (Some (ValueOf uni x)) = encode (Some $ TypeIn uni) <> bring (Proxy @Flat) uni (encode x)

    decode = go =<< decode where
        go (Some (TypeIn uni)) = Some . ValueOf uni <$> bring (Proxy @Flat) uni decode

    -- We need to get the flat instance in scope.
    size (Some (ValueOf uni x)) acc = size (Some $ TypeIn uni) acc
                                        + bring (Proxy @Flat) uni (size x 0)

instance Flat Unique where
    encode (Unique i) = eInt i
    decode = Unique <$> dInt
    -- There is no Generic instance for Unique,
    -- so a `size` function cannot be generated.
    size (Unique i) = sInt i

instance Flat Name where
    encode (Name txt u) = encode txt <> encode u
    decode = Name <$> decode <*> decode

instance Flat TyName where
    encode (TyName n) = encode n
    decode = TyName <$> decode

instance Flat ann => Flat (Version ann) where
    encode (Version ann n n' n'') = encode ann <> encode n <> encode n' <> encode n''
    decode = Version <$> decode <*> decode <*> decode <*> decode

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

    size tm sz = kindTagWidth + sz + case tm of
        Type ann           -> getSize ann
        KindArrow ann k k' -> getSize ann + getSize k + getSize k'

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

    decode = go =<< decodeType
        where go 0 = TyVar     <$> decode <*> decode
              go 1 = TyFun     <$> decode <*> decode <*> decode
              go 2 = TyIFix    <$> decode <*> decode <*> decode
              go 3 = TyForall  <$> decode <*> decode <*> decode <*> decode
              go 4 = TyBuiltin <$> decode <*> decode
              go 5 = TyLam     <$> decode <*> decode <*> decode <*> decode
              go 6 = TyApp     <$> decode <*> decode <*> decode
              go _ = fail "Failed to decode Type TyName ()"

    size tm sz = typeTagWidth + sz + case tm of
        TyVar     ann tn      -> getSize ann + getSize tn
        TyFun     ann t t'    -> getSize ann + getSize t   + getSize t'
        TyIFix    ann pat arg -> getSize ann + getSize pat + getSize arg
        TyForall  ann tn k t  -> getSize ann + getSize tn  + getSize k + getSize t
        TyBuiltin ann con     -> getSize ann + getSize con
        TyLam     ann n k t   -> getSize ann + getSize n   + getSize k + getSize t
        TyApp     ann t t'    -> getSize ann + getSize t   + getSize t'

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

    decode = go =<< decodeTerm
        where go 0 = Var      <$> decode <*> decode
              go 1 = TyAbs    <$> decode <*> decode <*> decode <*> decode
              go 2 = LamAbs   <$> decode <*> decode <*> decode <*> decode
              go 3 = Apply    <$> decode <*> decode <*> decode
              go 4 = Constant <$> decode <*> decode
              go 5 = TyInst   <$> decode <*> decode <*> decode
              go 6 = Unwrap   <$> decode <*> decode
              go 7 = IWrap    <$> decode <*> decode <*> decode <*> decode
              go 8 = Error    <$> decode <*> decode
              go 9 = Builtin  <$> decode <*> decode
              go _ = fail "Failed to decode Term TyName Name ()"

    size tm sz = termTagWidth + sz + case tm of
        Var      ann n         -> getSize ann + getSize n
        TyAbs    ann tn k t    -> getSize ann + getSize tn  + getSize k   + getSize t
        LamAbs   ann n ty t    -> getSize ann + getSize n   + getSize ty  + getSize t
        Apply    ann t t'      -> getSize ann + getSize t   + getSize t'
        Constant ann c         -> getSize ann + getSize c
        TyInst   ann t ty      -> getSize ann + getSize t   + getSize ty
        Unwrap   ann t         -> getSize ann + getSize t
        IWrap    ann pat arg t -> getSize ann + getSize pat + getSize arg + getSize t
        Error    ann ty        -> getSize ann + getSize ty
        Builtin  ann bn        -> getSize ann + getSize bn

instance ( Closed uni
         , Flat fun
         , Flat ann
         , Flat tyname
         , Flat name
         ) => Flat (VarDecl tyname name uni fun ann) where
    encode (VarDecl t name tyname ) = encode t <> encode name <> encode tyname
    decode = VarDecl <$> decode <*> decode <*> decode

instance (Flat ann, Flat tyname)  => Flat (TyVarDecl tyname ann) where
    encode (TyVarDecl t tyname kind) = encode t <> encode tyname <> encode kind
    decode = TyVarDecl <$> decode <*> decode <*> decode

instance ( Closed uni
         , uni `Everywhere` Flat
         , Flat fun
         , Flat ann
         , Flat tyname
         , Flat name
         ) => Flat (Program tyname name uni fun ann) where
    encode (Program ann v t) = encode ann <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode

deriving newtype instance (Flat a) => Flat (Normalized a)

instance Flat a => Flat (Token a)
-- instance Flat AlexPosn
instance Flat Keyword
instance Flat Special

deriving newtype instance Flat Index

instance Flat DeBruijn where
    encode (DeBruijn i) = encode i
    decode = DeBruijn <$> decode

instance Flat NamedDeBruijn where
    encode (NamedDeBruijn txt index) = encode txt <> encode index
    decode = NamedDeBruijn <$> decode <*> decode

instance Flat TyDeBruijn where
    encode (TyDeBruijn n) = encode n
    decode = TyDeBruijn <$> decode

instance Flat NamedTyDeBruijn where
    encode (NamedTyDeBruijn n) = encode n
    decode = NamedTyDeBruijn <$> decode

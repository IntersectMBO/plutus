{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Serialise instances for Plutus Core types. Make sure to read the
-- Note [Stable encoding of PLC] before touching anything in this
-- file.  Also see the Notes [Serialising unit annotations] and
-- [Serialising Scripts] before using anything in this file.

module Language.PlutusCore.CBOR ( encode
                                , decode
                                , OmitUnitAnnotations (..)
                                , serialiseOmittingUnits
                                , deserialiseRestoringUnits
                                , deserialiseRestoringUnitsOrFail
                                , DeserialiseFailure (..)
                                ) where
-- Codec.CBOR.DeserialiseFailure is re-exported from this module for use with deserialiseRestoringUnitsOrFail

import           Language.PlutusCore.Core
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.MkPlc      (TyVarDecl (..), VarDecl (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe
import           PlutusPrelude


import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import qualified Data.ByteString.Lazy           as BSL
import           Data.Proxy

{- Note [Stable encoding of PLC]
READ THIS BEFORE TOUCHING ANYTHING IN THIS FILE

We need the encoding of PLC on the blockchain to be *extremely* stable. It *must not* change
arbitrarily, otherwise we'll be unable to read back old transactions and validate them.

Consequently we don't use the derivable instances of `Serialise` for the PLC types that go
on the chain. (Also, the CBOR produced by those instances is more than 60% larger than that
produced by the instances below.)

However, the instances in this file *are* constrained by instances for names, type names,
and annotations. What's to stop the instances for *those* changing, thus changing
the overall encoding on the chain?

The answer is that what goes on the chain is *always* a `Program TyName Name ()`. The instances
for `TyName` and `Name` are nailed down here, and the instance for `()` is standard.

However, having this flexibility allows us to encode e.g. PLC with substantial annotations
(like position information) in situation where the stability is *not* critical, such as
for testing.
-}


{- [Note: Encoding/decoding constructor tags]
Use `encodeConstructorTag` and `decodeConstructorTag` to encode/decode
tags representing constructors.  These are just aliases for
`encodeWord` and `decodeWord`. Note that `encodeWord` is careful about
sizes and will only use one byte for the tags we have here.  NB: Don't
use encodeTag or decodeTag; those are for use with a fixed set of CBOR
tags with predefined meanings which we shouldn't interfere with.
See http://hackage.haskell.org/package/serialise.
-}

{- [Note: Don't use catamorphims!]
We use Codec.Serialise for encoding.  This uses an itermediate type
`Encoding` to encode things. `Encoding` is a monoid, which allows
subobjects to be encoded and then efficiently concatenated when a
larger object is being encoded to CBOR.  The monoid structure makes it
tempting to use catamoprhisms to encode things, but this is
*dangerous*. When a list is encoded to CBOR, the start of the list is
marked by a special token; this is then followed by the encodings of
the individual list elements, then another token to mark the end of
the list.  If we use a catamorphism to encode a list `l` it just
encodes the elements and concatenates the encoded versions together
without the markers, which is wrong: instead we should call `encode l`
directly.  At present we aren't encoding any lists, but we should take
care to avoid this trap just in case.
-}

encodeConstructorTag :: Word -> Encoding
encodeConstructorTag = encodeWord

decodeConstructorTag :: Decoder s Word
decodeConstructorTag = decodeWord

-- See Note [The G, the Tag and the Auto].
instance Closed uni => Serialise (Some (TypeIn uni)) where
    encode (Some (TypeIn uni)) = encodeConstructorTag . fromIntegral $ tagOf uni

    decode = go . uniAt . fromIntegral =<< decodeConstructorTag where
        go Nothing    = fail "Failed to decode a universe"
        go (Just uni) = pure uni

-- See Note [The G, the Tag and the Auto].
instance (Closed uni, uni `Everywhere` Serialise) => Serialise (Some (ValueOf uni)) where
    encode (Some (ValueOf uni x)) = encode (Some $ TypeIn uni) <> bring (Proxy @Serialise) uni (encode x)

    decode = go =<< decode where
        go (Some (TypeIn uni)) = Some . ValueOf uni <$> bring (Proxy @Serialise) uni decode

instance Serialise StaticBuiltinName where
    encode = encodeConstructorTag . \case
              AddInteger           -> 0
              SubtractInteger      -> 1
              MultiplyInteger      -> 2
              DivideInteger        -> 3
              RemainderInteger     -> 4
              LessThanInteger      -> 5
              LessThanEqInteger    -> 6
              GreaterThanInteger   -> 7
              GreaterThanEqInteger -> 8
              EqInteger            -> 9
              Concatenate          -> 10
              TakeByteString       -> 11
              DropByteString       -> 12
              SHA2                 -> 13
              SHA3                 -> 14
              VerifySignature      -> 15
              EqByteString         -> 16
              QuotientInteger      -> 17
              ModInteger           -> 18
              LtByteString         -> 19
              GtByteString         -> 20
              IfThenElse           -> 21

    decode = go =<< decodeConstructorTag
        where go 0  = pure AddInteger
              go 1  = pure SubtractInteger
              go 2  = pure MultiplyInteger
              go 3  = pure DivideInteger
              go 4  = pure RemainderInteger
              go 5  = pure LessThanInteger
              go 6  = pure LessThanEqInteger
              go 7  = pure GreaterThanInteger
              go 8  = pure GreaterThanEqInteger
              go 9  = pure EqInteger
              go 10 = pure Concatenate
              go 11 = pure TakeByteString
              go 12 = pure DropByteString
              go 13 = pure SHA2
              go 14 = pure SHA3
              go 15 = pure VerifySignature
              go 16 = pure EqByteString
              go 17 = pure QuotientInteger
              go 18 = pure ModInteger
              go 19 = pure LtByteString
              go 20 = pure GtByteString
              go 21 = pure IfThenElse
              go _  = fail "Failed to decode BuiltinName"

instance Serialise Unique where
    encode (Unique i) = encodeInt i
    decode = Unique <$> decodeInt

instance Serialise Name where
    -- TODO: should we encode the name or not?
    encode (Name txt u) = encode txt <> encode u
    decode = Name <$> decode <*> decode

instance Serialise TyName where
    encode (TyName n) = encode n
    decode = TyName <$> decode

instance Serialise ann => Serialise (Version ann) where
    encode (Version ann n n' n'') = encode ann <> encode n <> encode n' <> encode n''
    decode = Version <$> decode <*> decode <*> decode <*> decode

instance Serialise ann => Serialise (Kind ann) where
    encode = \case
        Type ann           -> encodeConstructorTag 0 <> encode ann
        KindArrow ann k k' -> encodeConstructorTag 1 <> encode ann <> encode k  <> encode k'

    decode = go =<< decodeConstructorTag
        where go 0 = Type      <$> decode
              go 1 = KindArrow <$> decode <*> decode <*> decode
              go _ = fail "Failed to decode Kind ()"

instance (Closed uni, Serialise ann, Serialise tyname) => Serialise (Type tyname uni ann) where
    encode = \case
        TyVar     ann tn      -> encodeConstructorTag 0 <> encode ann <> encode tn
        TyFun     ann t t'    -> encodeConstructorTag 1 <> encode ann <> encode t   <> encode t'
        TyIFix    ann pat arg -> encodeConstructorTag 2 <> encode ann <> encode pat <> encode arg
        TyForall  ann tn k t  -> encodeConstructorTag 3 <> encode ann <> encode tn  <> encode k <> encode t
        TyBuiltin ann con     -> encodeConstructorTag 4 <> encode ann <> encode con
        TyLam     ann n k t   -> encodeConstructorTag 5 <> encode ann <> encode n   <> encode k <> encode t
        TyApp     ann t t'    -> encodeConstructorTag 6 <> encode ann <> encode t   <> encode t'

    decode = go =<< decodeConstructorTag
        where go 0 = TyVar     <$> decode <*> decode
              go 1 = TyFun     <$> decode <*> decode <*> decode
              go 2 = TyIFix    <$> decode <*> decode <*> decode
              go 3 = TyForall  <$> decode <*> decode <*> decode <*> decode
              go 4 = TyBuiltin <$> decode <*> decode
              go 5 = TyLam     <$> decode <*> decode <*> decode <*> decode
              go 6 = TyApp     <$> decode <*> decode <*> decode
              go _ = fail "Failed to decode Type TyName ()"

instance Serialise DynamicBuiltinName where
    encode (DynamicBuiltinName name) = encode name
    decode = DynamicBuiltinName <$> decode

instance Serialise BuiltinName where
    encode (StaticBuiltinName bn) = encodeConstructorTag 0 <> encode bn
    encode (DynBuiltinName   dbn) = encodeConstructorTag 1 <> encode dbn

    decode = go =<< decodeConstructorTag
        where go 0 = StaticBuiltinName <$> decode
              go 1 = DynBuiltinName    <$> decode
              go _ = fail "Failed to decode Builtin ()"

instance ( Closed uni
         , uni `Everywhere` Serialise
         , Serialise ann
         , Serialise tyname
         , Serialise name
         ) => Serialise (Term tyname name uni ann) where
    encode = \case
        Var      ann n         -> encodeConstructorTag 0 <> encode ann <> encode n
        TyAbs    ann tn k t    -> encodeConstructorTag 1 <> encode ann <> encode tn  <> encode k   <> encode t
        LamAbs   ann n ty t    -> encodeConstructorTag 2 <> encode ann <> encode n   <> encode ty  <> encode t
        Apply    ann t t'      -> encodeConstructorTag 3 <> encode ann <> encode t   <> encode t'
        Constant ann c         -> encodeConstructorTag 4 <> encode ann <> encode c
        TyInst   ann t ty      -> encodeConstructorTag 5 <> encode ann <> encode t   <> encode ty
        Unwrap   ann t         -> encodeConstructorTag 6 <> encode ann <> encode t
        IWrap    ann pat arg t -> encodeConstructorTag 7 <> encode ann <> encode pat <> encode arg <> encode t
        Error    ann ty        -> encodeConstructorTag 8 <> encode ann <> encode ty
        Builtin  ann bn        -> encodeConstructorTag 9 <> encode ann <> encode bn

    decode = go =<< decodeConstructorTag
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

instance ( Closed uni
         , Serialise ann
         , Serialise tyname
         , Serialise name
         ) => Serialise (VarDecl tyname name uni ann) where
    encode (VarDecl t name tyname ) = encode t <> encode name <> encode tyname
    decode = VarDecl <$> decode <*> decode <*> decode

instance (Serialise ann, Serialise tyname)  => Serialise (TyVarDecl tyname ann) where
    encode (TyVarDecl t tyname kind) = encode t <> encode tyname <> encode kind
    decode = TyVarDecl <$> decode <*> decode <*> decode

instance ( Closed uni
         , uni `Everywhere` Serialise
         , Serialise ann
         , Serialise tyname
         , Serialise name
         ) => Serialise (Program tyname name uni ann) where
    encode (Program ann v t) = encode ann <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode

deriving newtype instance (Serialise a) => Serialise (Normalized a)

instance Serialise a => Serialise (Token a)
-- instance Serialise AlexPosn
instance Serialise Keyword
instance Serialise Special

deriving newtype instance Serialise Index

instance Serialise DeBruijn where
    encode (DeBruijn txt i) = encode txt <> encode i
    decode = DeBruijn <$> decode <*> decode

instance Serialise TyDeBruijn where
    encode (TyDeBruijn n) = encode n
    decode = TyDeBruijn <$> decode


{- Note [Serialising unit annotations]

Serialising the unit annotation takes up space: () is converted to the
CBOR `null` value, which is encoded as the byte 0xF6.  In typical
examples these account for 30% or more of the bytes in a serialised
PLC program.  We don't actually need to serialise unit annotations
since we know where they're going to appear when we're deserialising,
and we know what the value has to be.  The `InvisibleUnit` type below
has instances which takes care of this for us: if we have an
`InvisibleUnit`-annotated program `prog` then `serialise prog` will
serialise a program omitting the annotations, and `deserialise` (with
an appropriate type ascription) will give us back an
`InvisibleUnit`-annotated program.

We usually deal with ()-annotated ASTs, so the annotations have to be
converted to and from `InvisibleUnit` if we wish to save space.  The
obvious way to do this is to use `InvisibleUnit <$ ...` and
`() <$ ...`, but these have the disadvantage that they have to traverse the
entire AST and visit every annotation, adding an extra cost which may
be undesirable when deserialising things on-chain.  However,
`InvisibleUnit` has the same underlying representation as `()`, and
we can exploit this using Data.Coerce.coerce to convert entire ASTs
with no run-time overhead.
-}

newtype InvisibleUnit = InvisibleUnit ()

instance Serialise InvisibleUnit where
    encode = mempty
    decode = pure (InvisibleUnit ())

{- Note [Serialising Scripts]

At first sight, all we need to do to serialise a script without unit
annotations appearing in the CBOR is to coerce from `()` to
`InvisibleUnit` and then apply `serialise` as normal.  However, this
isn't sufficient for the ledger code. There are a number of places in
Ledger.Scripts and elsewhere where hashes of objects (`Tx`, for
example) are calculated by serialsing the entire object and
calculating a hash, and these objects can contain Scripts themselves.
Serialisation is achieved using the Generic instance of `Serialise`,
which will just use `encode` on everything, including unit
annotations.  we could overcome this by writing explicit `Serialise`
instances for everything.  This would be more space-efficient than the
Generic encoding, but would introduce a lot of extra code.  Instead,
we provide a wrapper class with an instance which performs the
coercions for us.  This is used in `Ledger.Scripts.Script` to
derive a suitable instance of `Serialise` for scripts. -}

newtype OmitUnitAnnotations uni  = OmitUnitAnnotations { restoreUnitAnnotations :: Program TyName Name uni () }
    deriving Serialise via Program TyName Name uni InvisibleUnit

{-| Convenience functions for serialisation/deserialisation without units -}
serialiseOmittingUnits :: (Closed uni, uni `Everywhere` Serialise) => Program TyName Name uni () -> BSL.ByteString
serialiseOmittingUnits = serialise . OmitUnitAnnotations

deserialiseRestoringUnits :: (Closed uni, uni `Everywhere` Serialise) => BSL.ByteString -> Program TyName Name uni ()
deserialiseRestoringUnits = restoreUnitAnnotations <$> deserialise

deserialiseRestoringUnitsOrFail :: (Closed uni, uni `Everywhere` Serialise) =>
                        BSL.ByteString -> Either DeserialiseFailure (Program TyName Name uni ())
deserialiseRestoringUnitsOrFail = second restoreUnitAnnotations <$> deserialiseOrFail

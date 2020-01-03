-- Serialisation without annotations.  We'lll only ever apply this to
-- stuff annotated with (), so we can safely omit it from the serialised code
-- and insert () when decoding

-- FIXME: We probably need special serialisation for names here as well.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Serialise instances for Plutus Core types. Make sure to read the Note [Stable encoding of PLC]
-- before touching anything in this file.
module Language.PlutusCore.Merkle.CBOR2 () where

import           Language.PlutusCore.CBOR         ()
--import           Language.PlutusCore.Merkle.Error
import           Language.PlutusCore.Merkle.MkPlc (TyVarDecl (..), VarDecl (..))
import           Language.PlutusCore.Merkle.Type
import           Language.PlutusCore.Name         ()
import           PlutusPrelude

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import           Crypto.Hash
import qualified Data.ByteArray                   as BA
import qualified Data.ByteString                  as BSS
import qualified Data.ByteString.Lazy             as BSL
import           Data.Functor.Foldable            hiding (fold)

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


{- Encode/decode constructor tags using encodeWord and decodeWord.  We
   previously used encodeTag/decodeTag here, but that was wrong: those
   are for use with a fixed set of CBOR tags with predefined meanings
   which we shouldn't interfere with.  Note that encodeWord will only
   use one byte for the tags we have here, so the size of the CBOR
   output doesn't change.
-}
encodeConstructorTag :: Word -> Encoding
encodeConstructorTag = encodeWord

decodeConstructorTag :: Decoder s Word
decodeConstructorTag = decodeWord


{- Serialising Digests from Crypto.Hash.  This is more complicated than
   you might expect.  If you say `encode = encode . BA.unpack` then
   the contents of the digest are unpacked into a `Word8` list with 32
   entries.  However, when cborg serialises a list, every element in
   the output is preceded by a type tag (in this case, 24), and this
   means that the serialised version is about 64 bytes long, twice the
   length of the original data.  Packing the `Word8` list into a
   `ByteString` fixes this because cborg just serialises this as a
   sequence of bytes. -}

{-
instance Serialise (Digest SHA256) where
    encode = encode . BSS.pack . BA.unpack
    decode = do
      d :: BSS.ByteString <- decode
      let bs :: BA.Bytes = BA.pack . BSS.unpack $ d
      case digestFromByteString bs of
        Nothing -> error $ "Couldn't decode SHA256 Digest: " ++ show d
        Just v  -> pure v
-}

-- FIXME: The above instance doesn't work because of an overlapping
-- instance in Ledger.Orphans.  However, I can't get the .cabal file
-- to include this in the build for this file

encodeDigest :: Digest SHA256 -> Encoding
encodeDigest = encode . BSS.pack. BA.unpack

decodeDigest :: Decoder s (Digest SHA256)
decodeDigest = do
      d :: BSS.ByteString <- decode
      let bs :: BA.Bytes = BA.pack . BSS.unpack $ d
      case digestFromByteString bs of
        Nothing -> error $ "Couldn't decode SHA256 Digest: " ++ show d
        Just v  -> pure v

instance Serialise (Kind ()) where
    encode = cata a where
        a (TypeF _)           = encodeConstructorTag 0
        a (KindArrowF _ k k') = fold [ encodeConstructorTag 1, k , k' ]

    decode = go =<< decodeConstructorTag
        where go 0 = Type <$> pure ()
              go 1 = KindArrow <$> pure () <*> decode <*> decode
              go _ = fail "Failed to decode Kind ()"

instance Serialise (tyname ()) => Serialise (Type tyname ()) where
    encode = cata a where
        a (TyVarF () tn)        = encodeConstructorTag 0 <> encode tn
        a (TyFunF () t t')      = encodeConstructorTag 1 <> t <> t'
        a (TyIFixF () pat arg)  = encodeConstructorTag 2 <> pat <> arg
        a (TyForallF () tn k t) = encodeConstructorTag 3 <> encode tn <> encode k <> t
        a (TyBuiltinF () con)   = encodeConstructorTag 4 <> encode con
        a (TyLamF () n k t)     = encodeConstructorTag 5 <> encode n <> encode k <> t
        a (TyAppF () t t')      = encodeConstructorTag 6 <> t <> t'
        a (TyPrunedF () h)      = encodeConstructorTag 7 <> encodeDigest h

    decode = go =<< decodeConstructorTag
        where go 0 = TyVar     <$> pure () <*> decode
              go 1 = TyFun     <$> pure () <*> decode <*> decode
              go 2 = TyIFix    <$> pure () <*> decode <*> decode
              go 3 = TyForall  <$> pure () <*> decode <*> decode <*> decode
              go 4 = TyBuiltin <$> pure () <*> decode
              go 5 = TyLam     <$> pure () <*> decode <*> decode <*> decode
              go 6 = TyApp     <$> pure () <*> decode <*> decode
              go 7 = TyPruned  <$> pure () <*> decodeDigest
              go _ = fail "Failed to decode Type TyName ()"

instance Serialise (Builtin ()) where
    encode (BuiltinName () bn)     = encodeConstructorTag 0 <> encode bn
    encode (DynBuiltinName () dbn) = encodeConstructorTag 1 <> encode dbn

    decode = go =<< decodeConstructorTag
        where go 0 = BuiltinName <$> pure () <*> decode
              go 1 = DynBuiltinName <$> pure () <*> decode
              go _ = fail "Failed to decode Builtin ()"


instance Serialise (Constant ()) where
    encode (BuiltinInt () i) = fold [ encodeConstructorTag 0, encodeInteger i ]
    encode (BuiltinBS () bs) = fold [ encodeConstructorTag 1, encodeBytes (BSL.toStrict bs) ]
    encode (BuiltinStr () s) = encodeConstructorTag 2 <> encode s
    decode = go =<< decodeConstructorTag
        where go 0 = BuiltinInt <$> pure () <*> decodeInteger
              go 1 = BuiltinBS <$> pure () <*> fmap BSL.fromStrict decodeBytes
              go 2 = BuiltinStr <$> pure () <*> decode
              go _ = fail "Failed to decode Constant ()"

instance ( Serialise (tyname ())
         , Serialise (name ())
         ) => Serialise (Term tyname name ()) where
    encode = cata a where
        a (VarF () n)           = encodeConstructorTag 0 <> encode n
        a (TyAbsF () tn k t)    = encodeConstructorTag 1 <> encode tn <> encode k <> t
        a (LamAbsF () n ty t)   = encodeConstructorTag 2 <> encode n <> encode ty <> t
        a (ApplyF () t t')      = encodeConstructorTag 3 <> t <> t'
        a (ConstantF () c)      = encodeConstructorTag 4 <> encode c
        a (TyInstF () t ty)     = encodeConstructorTag 5 <> t <> encode ty
        a (UnwrapF () t)        = encodeConstructorTag 6 <> t
        a (IWrapF () pat arg t) = encodeConstructorTag 7 <> encode pat <> encode arg <> t
        a (ErrorF () ty)        = encodeConstructorTag 8 <> encode ty
        a (BuiltinF () bi)      = encodeConstructorTag 9 <> encode bi
        a (PruneF () h)         = encodeConstructorTag 10 <> encodeDigest h

    decode = go =<< decodeConstructorTag
        where go 0  = Var <$> pure () <*> decode
              go 1  = TyAbs <$> pure () <*> decode <*> decode <*> decode
              go 2  = LamAbs <$> pure () <*> decode <*> decode <*> decode
              go 3  = Apply <$> pure () <*> decode <*> decode
              go 4  = Constant <$> pure () <*> decode
              go 5  = TyInst <$> pure () <*> decode <*> decode
              go 6  = Unwrap <$> pure () <*> decode
              go 7  = IWrap <$> pure () <*> decode <*> decode <*> decode
              go 8  = Error <$> pure () <*> decode
              go 9  = Builtin <$> pure () <*> decode
              go 10 = Prune <$> pure () <*> decodeDigest
              go _  = fail "Failed to decode Term TyName Name ()"

instance ( Serialise (tyname ())
         , Serialise (name ())
         ) => Serialise (VarDecl tyname name ()) where
    encode (VarDecl t name tyname ) = encode t <> encode name <> encode tyname
    decode = VarDecl <$> decode <*> decode <*> decode

instance Serialise (tyname ())  => Serialise (TyVarDecl tyname ()) where
    encode (TyVarDecl t tyname kind) = encode t <> encode tyname <> encode kind
    decode = TyVarDecl <$> decode <*> decode <*> decode

instance ( Serialise (tyname ())
         , Serialise (name ())
         ) => Serialise (Program tyname name ()) where
    encode (Program () v t) = encode v <> encode t  -- FIXME: do we want a tag here?
    decode = Program <$> pure () <*> decode <*> decode

deriving newtype instance Serialise (Normalized ())

{-
instance (Serialise ()) => Serialise (ParseError ())
instance (Serialise (tyname ()), Serialise ()) => Serialise (ValueRestrictionError tyname ())
instance (Serialise (tyname ()), Serialise (name ()), Serialise ()) =>
            Serialise (NormCheckError tyname name ())
instance (Serialise ()) => Serialise (UniqueError ())
instance Serialise UnknownDynamicBuiltinNameError
instance (Serialise ()) => Serialise (InternalTypeError ())
instance (Serialise ()) => Serialise (TypeError ())
instance (Serialise ()) => Serialise (Error ())
-}

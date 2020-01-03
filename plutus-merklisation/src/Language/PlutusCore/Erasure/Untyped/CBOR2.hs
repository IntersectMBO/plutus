-- Serialisation without annotations.  We'lll only ever apply this to
-- stuff annotated with (), so we can safely omit it from the serialised code
-- and insert () when decoding

-- FIXME: We probably need special serialisation for names here as well.

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Serialise instances for Plutus Core types. Make sure to read the Note [Stable encoding of PLC]
-- before touching anything in this file.
module Language.PlutusCore.Erasure.Untyped.CBOR2 () where

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import           Crypto.Hash
import qualified Data.ByteArray                                         as BA
import qualified Data.ByteString                                        as BSS
import qualified Data.ByteString.Lazy                                   as BSL
import           Data.Functor.Foldable                                  hiding (fold)

import qualified Language.PlutusCore.Core                               as PLC
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Erasure.Untyped.Instance.Recursive
import           Language.PlutusCore.Erasure.Untyped.Term
import           Language.PlutusCore.Name
import           PlutusPrelude

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

instance Serialise PLC.TypeBuiltin where
    encode bi = case bi of
        PLC.TyByteString -> encodeConstructorTag 0
        PLC.TyInteger    -> encodeConstructorTag 1
        PLC.TyString     -> encodeConstructorTag 2

    decode = go =<< decodeConstructorTag
        where go 0 = pure PLC.TyByteString
              go 1 = pure PLC.TyInteger
              go 2 = pure PLC.TyString
              go _ = fail "Failed to decode TypeBuiltin"

instance Serialise PLC.BuiltinName where
    encode bi =
        let i = case bi of
                PLC.AddInteger           -> 0
                PLC.SubtractInteger      -> 1
                PLC.MultiplyInteger      -> 2
                PLC.DivideInteger        -> 3
                PLC.RemainderInteger     -> 4
                PLC.LessThanInteger      -> 5
                PLC.LessThanEqInteger    -> 6
                PLC.GreaterThanInteger   -> 7
                PLC.GreaterThanEqInteger -> 8
                PLC.EqInteger            -> 9
                PLC.Concatenate          -> 10
                PLC.TakeByteString       -> 11
                PLC.DropByteString       -> 12
                PLC.SHA2                 -> 13
                PLC.SHA3                 -> 14
                PLC.VerifySignature      -> 15
                PLC.EqByteString         -> 16
                PLC.QuotientInteger      -> 17
                PLC.ModInteger           -> 18
                PLC.LtByteString         -> 19
                PLC.GtByteString         -> 20
        in encodeConstructorTag i

    decode = go =<< decodeConstructorTag
        where go 0  = pure PLC.AddInteger
              go 1  = pure PLC.SubtractInteger
              go 2  = pure PLC.MultiplyInteger
              go 3  = pure PLC.DivideInteger
              go 4  = pure PLC.RemainderInteger
              go 5  = pure PLC.LessThanInteger
              go 6  = pure PLC.LessThanEqInteger
              go 7  = pure PLC.GreaterThanInteger
              go 8  = pure PLC.GreaterThanEqInteger
              go 9  = pure PLC.EqInteger
              go 10 = pure PLC.Concatenate
              go 11 = pure PLC.TakeByteString
              go 12 = pure PLC.DropByteString
              go 13 = pure PLC.SHA2
              go 14 = pure PLC.SHA3
              go 15 = pure PLC.VerifySignature
              go 16 = pure PLC.EqByteString
              go 17 = pure PLC.QuotientInteger
              go 18 = pure PLC.ModInteger
              go 19 = pure PLC.LtByteString
              go 20 = pure PLC.GtByteString
              go _  = fail "Failed to decode BuiltinName"

instance Serialise Unique where
    encode (Unique i) = encodeInt i
    decode = Unique <$> decodeInt

instance Serialise (PLC.Version ()) where
    encode (PLC.Version () n n' n'') = fold [ encode n, encode n', encode n'' ]
    decode = PLC.Version <$> pure () <*> decode <*> decode <*> decode

instance Serialise PLC.DynamicBuiltinName where
    encode (PLC.DynamicBuiltinName name) = encode name
    decode = PLC.DynamicBuiltinName <$> decode

instance Serialise (Builtin ()) where
    encode (BuiltinName () bn)     = encodeConstructorTag 0 <> encode bn
    encode (DynBuiltinName () dbn) = encodeConstructorTag 1 <> encode dbn

    decode = go =<< decodeConstructorTag
        where go 0 = BuiltinName <$> pure () <*> decode
              go 1 = DynBuiltinName <$> pure () <*> decode
              go _ = fail "Failed to decode Builtin ()"

encodeDigest :: Digest SHA256 -> Encoding
encodeDigest = encode . BSS.pack. BA.unpack

decodeDigest :: Decoder s (Digest SHA256)
decodeDigest = do
      d :: BSS.ByteString <- decode
      let bs :: BA.Bytes = BA.pack . BSS.unpack $ d
      case digestFromByteString bs of
        Nothing -> error $ "Couldn't decode SHA256 Digest: " ++ show d
        Just v  -> pure v

instance Serialise (Constant ()) where
    encode (BuiltinInt () i) = fold [ encodeConstructorTag 0, encodeInteger i ]
    encode (BuiltinBS () bs) = fold [ encodeConstructorTag 1, encodeBytes (BSL.toStrict bs) ]
    encode (BuiltinStr () s) = encodeConstructorTag 2 <> encode s
    decode = go =<< decodeConstructorTag
        where go 0 = BuiltinInt <$> pure () <*> decodeInteger
              go 1 = BuiltinBS <$> pure () <*> fmap BSL.fromStrict decodeBytes
              go 2 = BuiltinStr <$> pure () <*> decode
              go _ = fail "Failed to decode Constant ()"

instance Serialise (name ()) => Serialise (Term name ()) where
    encode = cata a where
        a (VarF () n)      = encodeConstructorTag 0  <> encode n
        a (LamAbsF () n t) = encodeConstructorTag 1  <> encode n <> t
        a (ApplyF () t t') = encodeConstructorTag 2  <> t <> t'
        a (ConstantF () c) = encodeConstructorTag 3  <> encode c
        a (ErrorF ())      = encodeConstructorTag 4
        a (BuiltinF () bi) = encodeConstructorTag 5  <> encode bi
        a (PruneF () h)    = encodeConstructorTag 6  <> encodeDigest h

    decode = go =<< decodeConstructorTag
        where go 0 = Var <$> pure () <*> decode
              go 1 = LamAbs <$> pure () <*> decode <*> decode
              go 2 = Apply <$> pure () <*> decode <*> decode
              go 3 = Constant <$> pure () <*> decode
              go 4 = Error <$> pure ()
              go 5 = Builtin <$> pure () <*> decode
              go 6 = Prune <$> pure () <*> decodeDigest
              go _ = fail "Failed to decode Term Name ()"

instance Serialise (name ()) => Serialise (Program name ()) where
    encode (Program () v t) = encode v <> encode t  -- FIXME: do we need a tag here?
    decode = Program <$> pure () <*> decode <*> decode

deriving newtype instance (Serialise a) => Serialise (PLC.Normalized a)

deriving instance Serialise Index

instance Serialise (DeBruijn ()) where
    encode (DeBruijn () txt i) = encode txt <> encode i
    decode = DeBruijn <$> pure () <*> decode <*> decode

instance Serialise (TyDeBruijn ()) where
    encode (TyDeBruijn n) = encode n
    decode = TyDeBruijn <$> decode

{-
instance (Serialise a) => Serialise (ParseError a)
instance (Serialise a) => Serialise (UniqueError a)
instance Serialise UnknownDynamicBuiltinNameError
-}

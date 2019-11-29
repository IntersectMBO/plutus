{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Serialise instances for Plutus Core types. Make sure to read the Note [Stable encoding of PLC]
-- before touching anything in this file.
module Language.PlutusCore.Merkle.CBOR () where

import           Language.PlutusCore.Name ()
import           Language.PlutusCore.CBOR ()
import           Language.PlutusCore.Merkle.Error
import           Language.PlutusCore.Merkle.Type
import           Language.PlutusCore.Merkle.MkPlc      (TyVarDecl (..), VarDecl (..))
import           PlutusPrelude

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import           Crypto.Hash
import qualified Data.ByteArray                 as BA
import qualified Data.ByteString                as BSS
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable          hiding (fold)

{- Note [Stable encoding of PLC]
READ THIS BEFORE TOUCHING ANYTHING IN THIS FILE

We need the encoding of PLC on the blockchain to be *extremely* stable. It *must not* change
arbitrarily, otherwise we'll be unable to read back old transactions and validate them.

Consequently we don't use the derivable instances of `Serialise` for the PLC types that go
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


{- Serialising Digests.  This is more complicated than you might expect.
   If you say `encode = encode . BA.unpack` then the contents of the digest
   are unpacked into a `Word8` list with 32 entries.  However, when cborg
   serialises a list, every element in the output is preceded by a type 
   tag (in this case, 24), and this means that the serialised version
   is about 64 bytes long, twice the length of the original data.  Packing
   the `Word8` list into a `ByteString` fixes this because cborg just serialises
   this as a sequence of bytes. -}
instance Serialise (Digest SHA256) where
    encode = encode . BSS.pack . BA.unpack
    decode = do
      d :: [Word8] <- decode 
      let md = digestFromByteString . BSS.pack $ d
      case md of
        Nothing -> error $ "Couldn't decode SHA256 Digest: " ++ show d
        Just v  -> pure v

instance Serialise ann => Serialise (Kind ann) where
    encode = cata a where
        a (TypeF ann)           = encodeTag 0 <> encode ann
        a (KindArrowF ann k k') = fold [ encodeTag 1, encode ann, k , k' ]

    decode = go =<< decodeTag
        where go 0 = Type <$> decode
              go 1 = KindArrow <$> decode <*> decode <*> decode
              go _ = fail "Failed to decode Kind ()"

instance (Serialise ann, Serialise (tyname ann)) => Serialise (Type tyname ann) where
    encode = cata a where
        a (TyVarF ann tn)        = encodeTag 0 <> encode ann <> encode tn
        a (TyFunF ann t t')      = encodeTag 1 <> encode ann <> t <> t'
        a (TyIFixF ann pat arg)  = encodeTag 2 <> encode ann <> pat <> arg
        a (TyForallF ann tn k t) = encodeTag 3 <> encode ann <> encode tn <> encode k <> t
        a (TyBuiltinF ann con)   = encodeTag 4 <> encode ann <> encode con
        a (TyLamF ann n k t)     = encodeTag 5 <> encode ann <> encode n <> encode k <> t
        a (TyAppF ann t t')      = encodeTag 6 <> encode ann <> t <> t'
        a (TyPrunedF ann h)      = encodeTag 7 <> encode ann <> encode h
                                   
    decode = go =<< decodeTag
        where go 0 = TyVar <$> decode <*> decode
              go 1 = TyFun <$> decode <*> decode <*> decode
              go 2 = TyIFix <$> decode <*> decode <*> decode
              go 3 = TyForall <$> decode <*> decode <*> decode <*> decode
              go 4 = TyBuiltin <$> decode <*> decode
              go 5 = TyLam <$> decode <*> decode <*> decode <*> decode
              go 6 = TyApp <$> decode <*> decode <*> decode
              go 7 = TyPruned <$> decode <*> decode
              go _ = fail "Failed to decode Type TyName ()"

instance Serialise ann => Serialise (Builtin ann) where
    encode (BuiltinName ann bn)     = encodeTag 0 <> encode ann <> encode bn
    encode (DynBuiltinName ann dbn) = encodeTag 1 <> encode ann <> encode dbn

    decode = go =<< decodeTag
        where go 0 = BuiltinName <$> decode <*> decode
              go 1 = DynBuiltinName <$> decode <*> decode
              go _ = fail "Failed to decode Builtin ()"


instance Serialise ann => Serialise (Constant ann) where
    encode (BuiltinInt ann i) = fold [ encodeTag 0, encode ann, encodeInteger i ]
    encode (BuiltinBS ann bs) = fold [ encodeTag 1, encode ann, encodeBytes (BSL.toStrict bs) ]
    encode (BuiltinStr ann s) = encodeTag 2 <> encode ann <> encode s
    decode = go =<< decodeTag
        where go 0 = BuiltinInt <$> decode <*> decodeInteger
              go 1 = BuiltinBS <$> decode <*> fmap BSL.fromStrict decodeBytes
              go 2 = BuiltinStr <$> decode <*> decode
              go _ = fail "Failed to decode Constant ()"

instance ( Serialise ann
         , Serialise (tyname ann)
         , Serialise (name ann)
         ) => Serialise (Term tyname name ann) where
    encode = cata a where
        a (VarF ann n)           = encodeTag 0 <> encode ann <> encode n
        a (TyAbsF ann tn k t)    = encodeTag 1 <> encode ann <> encode tn <> encode k <> t
        a (LamAbsF ann n ty t)   = encodeTag 2 <> encode ann <> encode n <> encode ty <> t
        a (ApplyF ann t t')      = encodeTag 3 <> encode ann <> t <> t'
        a (ConstantF ann c)      = encodeTag 4 <> encode ann <> encode c
        a (TyInstF ann t ty)     = encodeTag 5 <> encode ann <> t <> encode ty
        a (UnwrapF ann t)        = encodeTag 6 <> encode ann <> t
        a (IWrapF ann pat arg t) = encodeTag 7 <> encode ann <> encode pat <> encode arg <> t
        a (ErrorF ann ty)        = encodeTag 8 <> encode ann <> encode ty
        a (BuiltinF ann bi)      = encodeTag 9 <> encode ann <> encode bi
        a (PruneF ann h)         = encodeTag 10 <> encode ann <> encode h

    decode = go =<< decodeTag
        where go 0 = Var <$> decode <*> decode
              go 1 = TyAbs <$> decode <*> decode <*> decode <*> decode
              go 2 = LamAbs <$> decode <*> decode <*> decode <*> decode
              go 3 = Apply <$> decode <*> decode <*> decode
              go 4 = Constant <$> decode <*> decode
              go 5 = TyInst <$> decode <*> decode <*> decode
              go 6 = Unwrap <$> decode <*> decode
              go 7 = IWrap <$> decode <*> decode <*> decode <*> decode
              go 8 = Error <$> decode <*> decode
              go 9 = Builtin <$> decode <*> decode
              go 10 = Prune <$> decode <*> decode
              go _ = fail "Failed to decode Term TyName Name ()"

instance ( Serialise ann
         , Serialise (tyname ann)
         , Serialise (name ann)
         ) => Serialise (VarDecl tyname name ann) where
    encode (VarDecl t name tyname ) = encode t <> encode name <> encode tyname
    decode = VarDecl <$> decode <*> decode <*> decode

instance (Serialise ann, Serialise (tyname ann))  => Serialise (TyVarDecl tyname ann) where
    encode (TyVarDecl t tyname kind) = encode t <> encode tyname <> encode kind
    decode = TyVarDecl <$> decode <*> decode <*> decode

instance ( Serialise ann
         , Serialise (tyname ann)
         , Serialise (name ann)
         ) => Serialise (Program tyname name ann) where
    encode (Program ann v t) = encode ann <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode

deriving newtype instance (Serialise a) => Serialise (Normalized a)

instance (Serialise ann) => Serialise (ParseError ann)
instance (Serialise (tyname ann), Serialise ann) => Serialise (ValueRestrictionError tyname ann)
instance (Serialise (tyname ann), Serialise (name ann), Serialise ann) =>
            Serialise (NormCheckError tyname name ann)
instance (Serialise ann) => Serialise (UniqueError ann)
instance Serialise UnknownDynamicBuiltinNameError
instance (Serialise ann) => Serialise (InternalTypeError ann)
instance (Serialise ann) => Serialise (TypeError ann)
instance (Serialise ann) => Serialise (Error ann)

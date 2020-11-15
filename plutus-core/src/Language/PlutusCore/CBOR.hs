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
                                , encodeConstructorTag
                                , decodeConstructorTag
                                ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.MkPlc      (TyVarDecl (..), VarDecl (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
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


{- Note [Encoding/decoding constructor tags]
Use `encodeConstructorTag` and `decodeConstructorTag` to encode/decode
tags representing constructors.  These are just aliases for
`encodeWord` and `decodeWord`. Note that `encodeWord` is careful about
sizes and will only use one byte for the tags we have here.  NB: Don't
use encodeTag or decodeTag; those are for use with a fixed set of CBOR
tags with predefined meanings which we shouldn't interfere with.
See http://hackage.haskell.org/package/serialise.
-}

{- Note [Don't use catamorphims!]
We use Codec.Serialise for encoding.  This uses an intermediate type
`Encoding` to encode things. `Encoding` is a monoid, which allows
subobjects to be encoded and then efficiently concatenated when a
larger object is being encoded to CBOR.  The monoid structure makes it
tempting to use catamorphisms to encode things, but this is
*dangerous*. When a list is encoded to CBOR, the start of the list is
marked by a special token; this is then followed by the encodings of
the individual list elements, then another token to mark the end of
the list.  If we use a catamorphism to encode a list `l` it just
encodes the elements and concatenates the encoded versions together
without the markers, which is wrong: instead we should call `encode l`
directly.
-}

encodeConstructorTag :: Word -> Encoding
encodeConstructorTag = encodeWord

decodeConstructorTag :: Decoder s Word
decodeConstructorTag = decodeWord

-- See Note [The G, the Tag and the Auto].
instance Closed uni => Serialise (Some (TypeIn uni)) where
    encode (Some (TypeIn uni)) = encode . map (fromIntegral :: Int -> Word) $ encodeUni uni

    decode = go . decodeUni . map (fromIntegral :: Word -> Int) =<< decode where
        go Nothing    = fail "Failed to decode a universe"
        go (Just uni) = pure uni

-- See Note [The G, the Tag and the Auto].
instance (Closed uni, uni `Everywhere` Serialise) => Serialise (Some (ValueOf uni)) where
    encode (Some (ValueOf uni x)) = encode (Some $ TypeIn uni) <> bring (Proxy @Serialise) uni (encode x)

    decode = go =<< decode where
        go (Some (TypeIn uni)) = Some . ValueOf uni <$> bring (Proxy @Serialise) uni decode

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

instance ( Closed uni
         , uni `Everywhere` Serialise
         , Serialise ann
         , Serialise tyname
         , Serialise name
         , Serialise fun
         ) => Serialise (Term tyname name uni fun ann) where
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
         ) => Serialise (VarDecl tyname name uni fun ann) where
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
         , Serialise fun
         ) => Serialise (Program tyname name uni fun ann) where
    encode (Program ann v t) = encode ann <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode

deriving newtype instance (Serialise a) => Serialise (Normalized a)

instance Serialise a => Serialise (Token a)
-- instance Serialise AlexPosn
instance Serialise Keyword
instance Serialise Special

deriving newtype instance Serialise Index

instance Serialise DeBruijn where
    encode (DeBruijn i) = encode i
    decode = DeBruijn <$> decode

instance Serialise TyDeBruijn where
    encode (TyDeBruijn n) = encode n
    decode = TyDeBruijn <$> decode

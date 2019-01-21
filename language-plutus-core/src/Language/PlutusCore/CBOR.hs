{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Serialise instances for Plutus Core types. Make sure to read the Note [Stable encoding of PLC]
-- before touching anything in this file.
module Language.PlutusCore.CBOR () where

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable          hiding (fold)
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Lexer      (AlexPosn)
import           Language.PlutusCore.Lexer.Type hiding (name)
import           Language.PlutusCore.MkPlc      (TyVarDecl (..), VarDecl (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

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

instance Serialise TypeBuiltin where
    encode bi = case bi of
        TyByteString -> encodeTag 0
        TyInteger    -> encodeTag 1
        TySize       -> encodeTag 2
        TyString     -> encodeTag 3

    decode = go =<< decodeTag
        where go 0 = pure TyByteString
              go 1 = pure TyInteger
              go 2 = pure TySize
              go 3 = pure TyString
              go _ = fail "Failed to decode TypeBuiltin"

instance Serialise BuiltinName where
    encode bi =
        let i = case bi of
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
                ResizeInteger        -> 10
                IntToByteString      -> 11
                Concatenate          -> 12
                TakeByteString       -> 13
                DropByteString       -> 14
                ResizeByteString     -> 15
                SHA2                 -> 16
                SHA3                 -> 17
                VerifySignature      -> 18
                EqByteString         -> 19
                TxHash               -> 20
                BlockNum             -> 21
                SizeOfInteger        -> 22
                QuotientInteger      -> 23
                ModInteger           -> 24
        in encodeTag i

    decode = go =<< decodeTag
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
              go 10 = pure ResizeInteger
              go 11 = pure IntToByteString
              go 12 = pure Concatenate
              go 13 = pure TakeByteString
              go 14 = pure DropByteString
              go 15 = pure ResizeByteString
              go 16 = pure SHA2
              go 17 = pure SHA3
              go 18 = pure VerifySignature
              go 19 = pure EqByteString
              go 20 = pure TxHash
              go 21 = pure BlockNum
              go 22 = pure SizeOfInteger
              go 23 = pure QuotientInteger
              go 24 = pure ModInteger
              go _  = fail "Failed to decode BuiltinName"

instance Serialise Unique where
    encode (Unique i) = encodeInt i
    decode = Unique <$> decodeInt

instance Serialise a => Serialise (Name a) where
    -- TODO: should we encode the name or not?
    encode (Name x txt u) = encode x <> encode txt <> encode u
    decode = Name <$> decode <*> decode <*> decode

instance Serialise a => Serialise (TyName a) where
    encode (TyName n) = encode n
    decode = TyName <$> decode

instance Serialise a => Serialise (Version a) where
    encode (Version x n n' n'') = fold [ encode x, encode n, encode n', encode n'' ]
    decode = Version <$> decode <*> decode <*> decode <*> decode

instance Serialise a => Serialise (Kind a) where
    encode = cata a where
        a (TypeF x)           = encodeTag 0 <> encode x
        a (KindArrowF x k k') = fold [ encodeTag 1, encode x, k , k' ]
        a (SizeF x)           = encodeTag 2 <> encode x

    decode = go =<< decodeTag
        where go 0 = Type <$> decode
              go 1 = KindArrow <$> decode <*> decode <*> decode
              go 2 = Size <$> decode
              go _ = fail "Failed to decode Kind ()"

instance (Serialise a, Serialise (tyname a)) => Serialise (Type tyname a) where
    encode = cata a where
        a (TyVarF x tn)        = encodeTag 0 <> encode x <> encode tn
        a (TyFunF x t t')      = encodeTag 1 <> encode x <> t <> t'
        a (TyIFixF x pat arg)  = encodeTag 2 <> encode x <> pat <> arg
        a (TyForallF x tn k t) = encodeTag 3 <> encode x <> encode tn <> encode k <> t
        a (TyBuiltinF x bi)    = encodeTag 4 <> encode x <> encode bi
        a (TyIntF x n)         = encodeTag 5 <> encode x <> encode n
        a (TyLamF x n k t)     = encodeTag 6 <> encode x <> encode n <> encode k <> t
        a (TyAppF x t t')      = encodeTag 7 <> encode x <> t <> t'

    decode = go =<< decodeTag
        where go 0 = TyVar <$> decode <*> decode
              go 1 = TyFun <$> decode <*> decode <*> decode
              go 2 = TyIFix <$> decode <*> decode <*> decode
              go 3 = TyForall <$> decode <*> decode <*> decode <*> decode
              go 4 = TyBuiltin <$> decode <*> decode
              go 5 = TyInt <$> decode <*> decode
              go 6 = TyLam <$> decode <*> decode <*> decode <*> decode
              go 7 = TyApp <$> decode <*> decode <*> decode
              go _ = fail "Failed to decode Type TyName ()"

instance Serialise DynamicBuiltinName where
    encode (DynamicBuiltinName name) = encode name
    decode = DynamicBuiltinName <$> decode

instance Serialise a => Serialise (Builtin a) where
    encode (BuiltinName x bn)     = encodeTag 0 <> encode x <> encode bn
    encode (DynBuiltinName x dbn) = encodeTag 1 <> encode x <> encode dbn

    decode = go =<< decodeTag
        where go 0 = BuiltinName <$> decode <*> decode
              go 1 = DynBuiltinName <$> decode <*> decode
              go _ = fail "Failed to decode Builtin ()"


instance Serialise a => Serialise (Constant a) where
    encode (BuiltinInt x n i) = fold [ encodeTag 0, encode x, encode n, encodeInteger i ]
    encode (BuiltinBS x n bs) = fold [ encodeTag 1, encode x, encode n, encodeBytes (BSL.toStrict bs) ]
    encode (BuiltinSize x n)  = encodeTag 2 <> encode x <> encode n
    encode (BuiltinStr x s)   = encodeTag 3 <> encode x <> encode s
    decode = go =<< decodeTag
        where go 0 = BuiltinInt <$> decode <*> decode <*> decodeInteger
              go 1 = BuiltinBS <$> decode <*> decode <*> fmap BSL.fromStrict decodeBytes
              go 2 = BuiltinSize <$> decode <*> decode
              go 3 = BuiltinStr <$> decode <*> decode
              go _ = fail "Failed to decode Constant ()"

instance (Serialise a, Serialise (tyname a), Serialise (name a)) => Serialise (Term tyname name a) where
    encode = cata a where
        a (VarF x n)           = encodeTag 0 <> encode x <> encode n
        a (TyAbsF x tn k t)    = encodeTag 1 <> encode x <> encode tn <> encode k <> t
        a (LamAbsF x n ty t)   = encodeTag 2 <> encode x <> encode n <> encode ty <> t
        a (ApplyF x t t')      = encodeTag 3 <> encode x <> t <> t'
        a (ConstantF x c)      = encodeTag 4 <> encode x <> encode c
        a (TyInstF x t ty)     = encodeTag 5 <> encode x <> t <> encode ty
        a (UnwrapF x t)        = encodeTag 6 <> encode x <> t
        a (IWrapF x pat arg t) = encodeTag 7 <> encode x <> encode pat <> encode arg <> t
        a (ErrorF x ty)        = encodeTag 8 <> encode x <> encode ty
        a (BuiltinF x bi)      = encodeTag 9 <> encode x <> encode bi

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
              go _ = fail "Failed to decode Term TyName Name ()"

instance (Serialise a, Serialise (tyname a), Serialise (name a)) => Serialise (VarDecl tyname name a) where
    encode (VarDecl t name tyname ) = encode t <> encode name <> encode tyname
    decode = VarDecl <$> decode <*> decode <*> decode

instance (Serialise a, Serialise (tyname a))  => Serialise (TyVarDecl tyname a) where
    encode (TyVarDecl t tyname kind) = encode t <> encode tyname <> encode kind
    decode = TyVarDecl <$> decode <*> decode <*> decode

instance (Serialise a, Serialise (tyname a), Serialise (name a)) => Serialise (Program tyname name a) where
    encode (Program x v t) = encode x <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode

instance Serialise AlexPosn

deriving instance Serialise Index

instance Serialise a => Serialise (DeBruijn a) where
    encode (DeBruijn x txt i) = encode x <> encode txt <> encode i
    decode = DeBruijn <$> decode <*> decode <*> decode

instance Serialise a => Serialise (TyDeBruijn a) where
    encode (TyDeBruijn n) = encode n
    decode = TyDeBruijn <$> decode

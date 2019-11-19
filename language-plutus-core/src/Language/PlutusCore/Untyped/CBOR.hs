{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Serialise instances for Plutus Core types. Make sure to read the Note [Stable encoding of PLC]
-- before touching anything in this file.
module Language.PlutusCore.Untyped.CBOR () where

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable          hiding (fold)
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer      (AlexPosn)
import           Language.PlutusCore.Lexer.Type hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Untyped.Term
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
        TyString     -> encodeTag 2

    decode = go =<< decodeTag
        where go 0 = pure TyByteString
              go 1 = pure TyInteger
              go 2 = pure TyString
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
              go _  = fail "Failed to decode BuiltinName"

instance Serialise Unique where
    encode (Unique i) = encodeInt i
    decode = Unique <$> decodeInt

instance Serialise a => Serialise (Version a) where
    encode (Version x n n' n'') = fold [ encode x, encode n, encode n', encode n'' ]
    decode = Version <$> decode <*> decode <*> decode <*> decode

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
    encode (BuiltinInt x i) = fold [ encodeTag 0, encode x, encodeInteger i ]
    encode (BuiltinBS x bs) = fold [ encodeTag 1, encode x, encodeBytes (BSL.toStrict bs) ]
    encode (BuiltinStr x s) = encodeTag 2 <> encode x <> encode s
    decode = go =<< decodeTag
        where go 0 = BuiltinInt <$> decode <*> decodeInteger
              go 1 = BuiltinBS <$> decode <*> fmap BSL.fromStrict decodeBytes
              go 2 = BuiltinStr <$> decode <*> decode
              go _ = fail "Failed to decode Constant ()"

instance (Serialise a, Serialise (name a)) => Serialise (Term name a) where
    encode = cata a where
        a (VarF x n)           = encodeTag 0 <> encode x <> encode n
        a (LamAbsF x n t)      = encodeTag 1 <> encode x <> encode n <> t
        a (ApplyF x t t')      = encodeTag 2 <> encode x <> t <> t'
        a (ConstantF x c)      = encodeTag 3 <> encode x <> encode c
        a (ErrorF x)           = encodeTag 4 <> encode x
        a (BuiltinF x bi)      = encodeTag 5 <> encode x <> encode bi

    decode = go =<< decodeTag
        where go 0 = Var <$> decode <*> decode
              go 1 = LamAbs <$> decode <*> decode <*> decode
              go 2 = Apply <$> decode <*> decode <*> decode
              go 3 = Constant <$> decode <*> decode
              go 4 = Error <$> decode
              go 5 = Builtin <$> decode <*> decode
              go _ = fail "Failed to decode Term Name ()"

instance (Serialise a, Serialise (name a)) => Serialise (Program name a) where
    encode (Program x v t) = encode x <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode

deriving newtype instance (Serialise a) => Serialise (Normalized a)

instance Serialise a => Serialise (Token a)
instance Serialise AlexPosn
instance Serialise Keyword
instance Serialise Special

deriving instance Serialise Index

instance Serialise a => Serialise (DeBruijn a) where
    encode (DeBruijn x txt i) = encode x <> encode txt <> encode i
    decode = DeBruijn <$> decode <*> decode <*> decode

instance Serialise a => Serialise (TyDeBruijn a) where
    encode (TyDeBruijn n) = encode n
    decode = TyDeBruijn <$> decode

instance (Serialise a) => Serialise (ParseError a)
instance (Serialise a) => Serialise (UniqueError a)
instance Serialise UnknownDynamicBuiltinNameError

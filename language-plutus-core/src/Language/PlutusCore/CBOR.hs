{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.PlutusCore.CBOR () where

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable          hiding (fold)
import           Language.PlutusCore.MkPlc      (TyVarDecl(..), VarDecl(..))
import           Language.PlutusCore.Lexer.Type hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

instance Serialise TypeBuiltin where
    encode bi =
        let i = case bi of
                TyByteString -> 0
                TyInteger    -> 1
                TySize       -> 2
        in encodeTag i

    decode = go =<< decodeTag
        where go 0 = pure TyByteString
              go 1 = pure TyInteger
              go 2 = pure TySize
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

instance Serialise (Name ()) where
    -- TODO: should we encode the name or not?
    encode (Name _ bs u) = encodeBytes (BSL.toStrict bs) <> encode u
    decode = Name () <$> fmap BSL.fromStrict decodeBytes <*> decode

instance Serialise (TyName ()) where
    encode (TyName n) = encode n
    decode = TyName <$> decode

instance Serialise (Version ()) where
    encode (Version _ n n' n'') = fold [ encode n, encode n', encode n'' ]
    decode = Version () <$> decode <*> decode <*> decode

instance Serialise (Kind ()) where
    encode = cata a where
        a TypeF{}             = encodeTag 0
        a (KindArrowF _ k k') = fold [ encodeTag 1, k , k' ]
        a SizeF{}             = encodeTag 2

    decode = go =<< decodeTag
        where go 0 = pure (Type ())
              go 1 = KindArrow () <$> decode <*> decode
              go 2 = pure (Size ())
              go _ = fail "Failed to decode Kind ()"

instance Serialise (tyname ()) => Serialise (Type tyname ()) where
    encode = cata a where
        a (TyVarF _ tn)        = encodeTag 0 <> encode tn
        a (TyFunF _ t t')      = encodeTag 1 <> t <> t'
        a (TyFixF _ tn t)      = encodeTag 2 <> encode tn <> t
        a (TyForallF _ tn k t) = encodeTag 3 <> encode tn <> encode k <> t
        a (TyBuiltinF _ bi)    = encodeTag 4 <> encode bi
        a (TyIntF _ n)         = encodeTag 5 <> encode n
        a (TyLamF _ n k t)     = encodeTag 6 <> encode n <> encode k <> t
        a (TyAppF _ t t')      = encodeTag 7 <> t <> t'

    decode = go =<< decodeTag
        where go 0 = TyVar () <$> decode
              go 1 = TyFun () <$> decode <*> decode
              go 2 = TyFix () <$> decode <*> decode
              go 3 = TyForall () <$> decode <*> decode <*> decode
              go 4 = TyBuiltin () <$> decode
              go 5 = TyInt () <$> decode
              go 6 = TyLam () <$> decode <*> decode <*> decode
              go 7 = TyApp () <$> decode <*> decode
              go _ = fail "Failed to decode Type TyName ()"

instance Serialise DynamicBuiltinName where
    encode (DynamicBuiltinName name) = encode name
    decode = DynamicBuiltinName <$> decode

instance Serialise (Constant ()) where
    encode (BuiltinInt _ n i)     = fold [ encodeTag 0, encode n, encodeInteger i ]
    encode (BuiltinBS _ n bs)     = fold [ encodeTag 1, encode n, encodeBytes (BSL.toStrict bs) ]
    encode (BuiltinSize _ n)      = encodeTag 2 <> encode n
    encode (BuiltinName _ bn)     = encodeTag 3 <> encode bn
    encode (DynBuiltinName _ dbn) = encodeTag 4 <> encode dbn

    decode = go =<< decodeTag
        where go 0 = BuiltinInt () <$> decode <*> decodeInteger
              go 1 = BuiltinBS () <$> decode <*> fmap BSL.fromStrict decodeBytes
              go 2 = BuiltinSize () <$> decode
              go 3 = BuiltinName () <$> decode
              go 4 = DynBuiltinName () <$> decode
              go _ = fail "Failed to decode Constant ()"

instance (Serialise (tyname ()), Serialise (name ())) => Serialise (Term tyname name ()) where
    encode = cata a where
        a (VarF _ n)         = encodeTag 0 <> encode n
        a (TyAbsF _ tn k t)  = encodeTag 1 <> encode tn <> encode k <> t
        a (LamAbsF _ n ty t) = encodeTag 2 <> encode n <> encode ty <> t
        a (ApplyF _ t t')    = encodeTag 3 <> t <> t'
        a (ConstantF _ c)    = encodeTag 4 <> encode c
        a (TyInstF _ t ty)   = encodeTag 5 <> t <> encode ty
        a (UnwrapF _ t)      = encodeTag 6 <> t
        a (WrapF _ tn ty t)  = encodeTag 7 <> encode tn <> encode ty <> t
        a (ErrorF _ ty)      = encodeTag 8 <> encode ty

    decode = go =<< decodeTag
        where go 0 = Var () <$> decode
              go 1 = TyAbs () <$> decode <*> decode <*> decode
              go 2 = LamAbs () <$> decode <*> decode <*> decode
              go 3 = Apply () <$> decode <*> decode
              go 4 = Constant () <$> decode
              go 5 = TyInst () <$> decode <*> decode
              go 6 = Unwrap () <$> decode
              go 7 = Wrap () <$> decode <*> decode <*> decode
              go 8 = Error () <$> decode
              go _ = fail "Failed to decode Term TyName Name ()"

instance (Serialise (tyname ()), Serialise (name ())) => Serialise (Program tyname name ()) where
    encode (Program _ v t) = encode v <> encode t
    decode = Program () <$> decode <*> decode

instance (Serialise (tyname ()), Serialise (name ())) => Serialise (VarDecl tyname name ()) where
    encode (VarDecl tyname name _) = encode name <> encode tyname
    decode = VarDecl () <$> decode <*> decode

instance Serialise (tyname ())  => Serialise (TyVarDecl tyname () ) where
    encode (TyVarDecl _ tyname kind) = encode tyname <> encode kind
    decode = TyVarDecl () <$> decode <*> decode

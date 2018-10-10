module Language.PlutusCore.CBOR ( encodeProgram
                                , decodeProgram
                                , readProgram
                                , writeProgram
                                ) where

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.CBOR.Read
import           Codec.CBOR.Write
import qualified Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable          hiding (fold)
import           Language.PlutusCore.Lexer.Type hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

encodeTyBuiltin :: TypeBuiltin -> Encoding
encodeTyBuiltin bi =
    let i = case bi of
            TyByteString -> 0
            TyInteger    -> 1
            TySize       -> 2
    in encodeTag i

decodeTyBuiltin :: Decoder s TypeBuiltin
decodeTyBuiltin = go =<< decodeTag
    where go 0 = pure TyByteString
          go 1 = pure TyInteger
          go 2 = pure TySize
          go _ = fail "Failed to decode TypeBuiltin"

encodeBuiltinName :: BuiltinName -> Encoding
encodeBuiltinName bi =
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
    in encodeTag i

decodeBuiltinName :: Decoder s BuiltinName
decodeBuiltinName = go =<< decodeTag
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
          go _  = fail "Failed to decode BuiltinName"

encodeDynamicBuiltinName :: DynamicBuiltinName -> Encoding
encodeDynamicBuiltinName (DynamicBuiltinName name) = encodeString name

decodeDynamicBuiltinName :: Decoder s DynamicBuiltinName
decodeDynamicBuiltinName = DynamicBuiltinName <$> decodeString

encodeNatural :: Natural -> Encoding
encodeNatural = encodeInteger . fromIntegral

decodeNatural :: Decoder s Natural
decodeNatural = fromIntegral <$> decodeInteger

encodeUnique :: Unique -> Encoding
encodeUnique (Unique i) = encodeInt i

decodeUnique :: Decoder s Unique
decodeUnique = Unique <$> decodeInt

-- TODO: should we encode the name or not?
encodeName :: Name a -> Encoding
encodeName (Name _ bs u) = encodeBytes (BSL.toStrict bs) <> encodeUnique u

decodeName :: Decoder s (Name ())
decodeName = Name () <$> fmap BSL.fromStrict decodeBytes <*> decodeUnique

encodeTyName :: TyName a -> Encoding
encodeTyName (TyName n) = encodeName n

decodeTyName :: Decoder s (TyName ())
decodeTyName = TyName <$> decodeName

encodeVersion :: Version a -> Encoding
encodeVersion (Version _ n n' n'') = fold [ encodeNatural n, encodeNatural n', encodeNatural n'' ]

decodeVersion :: Decoder s (Version ())
decodeVersion = Version () <$> decodeNatural <*> decodeNatural <*> decodeNatural

encodeKind :: Kind a -> Encoding
encodeKind = cata a where
    a TypeF{}             = encodeTag 0
    a (KindArrowF _ k k') = fold [ encodeTag 1, k , k' ]
    a SizeF{}             = encodeTag 2

decodeKind :: Decoder s (Kind ())
decodeKind = go =<< decodeTag
    where go 0 = pure (Type ())
          go 1 = KindArrow () <$> decodeKind <*> decodeKind
          go 2 = pure (Size ())
          go _ = fail "Failed to decode Kind ()"

encodeType :: Type TyName a -> Encoding
encodeType = cata a where
    a (TyVarF _ tn)        = encodeTag 0 <> encodeTyName tn
    a (TyFunF _ t t')      = encodeTag 1 <> t <> t'
    a (TyFixF _ tn t)      = encodeTag 2 <> encodeTyName tn <> t
    a (TyForallF _ tn k t) = encodeTag 3 <> encodeTyName tn <> encodeKind k <> t
    a (TyBuiltinF _ bi)    = encodeTag 4 <> encodeTyBuiltin bi
    a (TyIntF _ n)         = encodeTag 5 <> encodeNatural n
    a (TyLamF _ n k t)     = encodeTag 6 <> encodeTyName n <> encodeKind k <> t
    a (TyAppF _ t t')      = encodeTag 7 <> t <> t'

decodeType :: Decoder a (Type TyName ())
decodeType = go =<< decodeTag
    where go 0 = TyVar () <$> decodeTyName
          go 1 = TyFun () <$> decodeType <*> decodeType
          go 2 = TyFix () <$> decodeTyName <*> decodeType
          go 3 = TyForall () <$> decodeTyName <*> decodeKind <*> decodeType
          go 4 = TyBuiltin () <$> decodeTyBuiltin
          go 5 = TyInt () <$> decodeNatural
          go 6 = TyLam () <$> decodeTyName <*> decodeKind <*> decodeType
          go 7 = TyApp () <$> decodeType <*> decodeType
          go _ = fail "Failed to decode Type TyName ()"

encodeConstant :: Constant a -> Encoding
encodeConstant (BuiltinInt _ n i)     = fold [ encodeTag 0, encodeNatural n, encodeInteger i ]
encodeConstant (BuiltinBS _ n bs)     = fold [ encodeTag 1, encodeNatural n, encodeBytes (BSL.toStrict bs) ]
encodeConstant (BuiltinSize _ n)      = encodeTag 2 <> encodeNatural n
encodeConstant (BuiltinName _ bn)     = encodeTag 3 <> encodeBuiltinName bn
encodeConstant (DynBuiltinName _ dbn) = encodeTag 4 <> encodeDynamicBuiltinName dbn

decodeConstant :: Decoder s (Constant ())
decodeConstant = go =<< decodeTag
    where go 0 = BuiltinInt () <$> decodeNatural <*> decodeInteger
          go 1 = BuiltinBS () <$> decodeNatural <*> fmap BSL.fromStrict decodeBytes
          go 2 = BuiltinSize () <$> decodeNatural
          go 3 = BuiltinName () <$> decodeBuiltinName
          go 4 = DynBuiltinName () <$> decodeDynamicBuiltinName
          go _ = fail "Failed to decode Constant ()"

encodeTerm :: Term TyName Name a -> Encoding
encodeTerm = cata a where
    a (VarF _ n)         = encodeTag 0 <> encodeName n
    a (TyAbsF _ tn k t)  = encodeTag 1 <> encodeTyName tn <> encodeKind k <> t
    a (LamAbsF _ n ty t) = encodeTag 2 <> encodeName n <> encodeType ty <> t
    a (ApplyF _ t t')    = encodeTag 3 <> t <> t'
    a (ConstantF _ c)    = encodeTag 4 <> encodeConstant c
    a (TyInstF _ t ty)   = encodeTag 5 <> t <> encodeType ty
    a (UnwrapF _ t)      = encodeTag 6 <> t
    a (WrapF _ tn ty t)  = encodeTag 7 <> encodeTyName tn <> encodeType ty <> t
    a (ErrorF _ ty)      = encodeTag 8 <> encodeType ty

decodeTerm :: Decoder s (Term TyName Name ())
decodeTerm = go =<< decodeTag
    where go 0 = Var () <$> decodeName
          go 1 = TyAbs () <$> decodeTyName <*> decodeKind <*> decodeTerm
          go 2 = LamAbs () <$> decodeName <*> decodeType <*> decodeTerm
          go 3 = Apply () <$> decodeTerm <*> decodeTerm
          go 4 = Constant () <$> decodeConstant
          go 5 = TyInst () <$> decodeTerm <*> decodeType
          go 6 = Unwrap () <$> decodeTerm
          go 7 = Wrap () <$> decodeTyName <*> decodeType <*> decodeTerm
          go 8 = Error () <$> decodeType
          go _ = fail "Failed to decode Term TyName Name ()"

-- | Encode a program. For use with the @cborg@ library.
encodeProgram :: Program TyName Name a -> Encoding
encodeProgram (Program _ v t) = encodeVersion v <> encodeTerm t

-- | 'Decoder' for a 'Program'
decodeProgram :: Decoder s (Program TyName Name ())
decodeProgram = Program () <$> decodeVersion <*> decodeTerm

-- | Encode a program as a 'ByteString'
writeProgram :: Program TyName Name a -> BSL.ByteString
writeProgram = toLazyByteString . encodeProgram

-- | Attempt to deserialize a 'Program' form a 'ByteString'
readProgram :: BSL.ByteString -> Either DeserialiseFailure (Program TyName Name ())
readProgram = fmap snd . deserialiseFromBytes decodeProgram

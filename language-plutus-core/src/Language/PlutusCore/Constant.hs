{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
module Language.PlutusCore.Constant ( ConstAppResult(..)
                                    , ConstAppError(..)
                                    , IterApp(..)
                                    , TypedBuiltinSized(..)
                                    , TypedBuiltin(..)
                                    , viewPrimIterApp
                                    , applyBuiltinName
                                    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name

import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.ByteString.Lazy as BSL

newtype PairT b f a = PairT
    { unPairT :: f (b, a)
    }

instance Functor f => Functor (PairT b f) where
    fmap f (PairT p) = PairT $ fmap (fmap f) p
    {-# INLINE fmap #-}

-- | The type of constant applications errors.
data ConstAppError
    = SizeMismatchConstAppError Size (Constant ())
    | forall a. IllTypedConstAppError (TypedBuiltinSized a) (Constant ())
    | ExcessArgumentsConstAppErr [Constant ()]

data ConstAppResult
    = ConstAppSuccess (Term TyName Name ())
    | ConstAppFailure
    | ConstAppStuck
    | ConstAppError ConstAppError

-- | A function (called "head") applied to a list of arguments (called "spine").
data IterApp head arg = IterApp
    { _iterAppHead  :: head
    , _iterAppSpine :: [arg]
    }

type TermIterApp tyname name a =
    IterApp (Term tyname name a) (Term tyname name a)

type PrimIterApp =
    IterApp BuiltinName (Constant ())

-- | View a `Constant` as a `BuiltinName`.
viewBuiltinName :: Constant a -> Maybe BuiltinName
viewBuiltinName (BuiltinName _ name) = Just name
viewBuiltinName _                    = Nothing

-- | View a `Term` as a `Constant`.
viewConstant :: Term tyname name a -> Maybe (Constant a)
viewConstant (Constant _ constant) = Just constant
viewConstant _                     = Nothing

-- | View a `Term` as an `IterApp`.
viewTermIterApp :: Term tyname name a -> Maybe (TermIterApp tyname name a)
viewTermIterApp term@Apply{} = Just $ go [] term where
    go args (Apply _ fun arg) = go (undefined arg : args) fun
    go args  fun              = IterApp fun args
viewTermIterApp _            = Nothing

-- | View a `Term` as an iterated application of a `BuiltinName` to a list of `Constants`.
viewPrimIterApp :: Term tyname name () -> Maybe PrimIterApp
viewPrimIterApp term = do
    IterApp termHead termSpine <- viewTermIterApp term
    headName <- viewConstant termHead >>= viewBuiltinName
    spine <- traverse viewConstant termSpine
    Just $ IterApp headName spine

type Size = Natural

checkBoundsInt :: Size -> Integer -> Bool
checkBoundsInt s i = -2 ^ p <= i && i < 2 ^ p where
    p = 8 * fromIntegral s - 1 :: Int

checkBoundsBS :: Size -> BSL.ByteString -> Bool
checkBoundsBS = undefined

makeBuiltinInt :: Size -> Integer -> ConstAppResult
makeBuiltinInt size int
    | checkBoundsInt size int = ConstAppSuccess . Constant () $ BuiltinInt () size int
    | otherwise               = ConstAppFailure

makeBuiltinBS :: Size -> BSL.ByteString -> ConstAppResult
makeBuiltinBS size bs
    | checkBoundsBS size bs = ConstAppSuccess . Constant () $ BuiltinBS () size bs
    | otherwise             = ConstAppFailure

makeBuiltinSize :: Size -> Size -> ConstAppResult
makeBuiltinSize size size'
    | size == size' = ConstAppSuccess . Constant () $ BuiltinSize () size
    | otherwise     = ConstAppFailure

builtinTrue :: Term TyName Name a
builtinTrue = undefined

builtinFalse :: Term TyName Name a
builtinFalse = undefined

makeBuiltinBool :: Bool -> ConstAppResult
makeBuiltinBool b = ConstAppSuccess $ if b then builtinTrue else builtinFalse

infixr 9 `TypeSchemaArrow`

newtype SizeVar = SizeVar Int

newtype SizeValues = SizeValues (IntMap Size)

instance Enum SizeVar where
    toEnum = SizeVar
    fromEnum (SizeVar sizeIndex) = sizeIndex

data TypedBuiltinSized a where
    TypedBuiltinInt  :: TypedBuiltinSized Integer
    TypedBuiltinBS   :: TypedBuiltinSized BSL.ByteString
    TypedBuiltinSize :: TypedBuiltinSized Size

data TypedBuiltin a where
    TypedBuiltinSized :: SizeVar -> TypedBuiltinSized a -> TypedBuiltin a
    TypedBuiltinBool  :: TypedBuiltin Bool

data TypeSchema a where
    TypeSchemaBuiltin :: TypedBuiltin a -> TypeSchema a
    TypeSchemaArrow   :: TypeSchema a -> TypeSchema b -> TypeSchema (a -> b)
    TypeSchemaForall  :: (SizeVar -> TypeSchema a) -> TypeSchema a

data TypedBuiltinName a = TypedBuiltinName BuiltinName (TypeSchema a)

instance Pretty (TypedBuiltinSized a) where
    pretty = undefined

instance Pretty (TypedBuiltin a) where
    pretty = undefined

checkBuiltinSize :: Maybe Size -> Size -> Constant () -> b -> Either ConstAppError (b, Size)
checkBuiltinSize (Just size) size' constant _ | size /= size' =
    Left $ SizeMismatchConstAppError size constant
checkBuiltinSize  _          size' _        y = Right (y, size')

applyToSizedBuiltin
    :: TypedBuiltinSized a -> Maybe Size -> (a -> b) -> Constant () -> Either ConstAppError (b, Size)
applyToSizedBuiltin TypedBuiltinInt  maySize f constant@(BuiltinInt  () size' int) =
    checkBuiltinSize maySize size' constant (f int)
applyToSizedBuiltin TypedBuiltinBS   maySize f constant@(BuiltinBS   () size' bs ) =
    checkBuiltinSize maySize size' constant (f bs)
applyToSizedBuiltin TypedBuiltinSize maySize f constant@(BuiltinSize () size'    ) =
    checkBuiltinSize maySize size' constant (f size')
applyToSizedBuiltin typedBuiltin     _       _ constant                            =
    Left $ IllTypedConstAppError typedBuiltin constant

applyToBuiltin
    :: TypedBuiltin a -> SizeValues -> (a -> b) -> Constant () -> Either ConstAppError (b, SizeValues)
applyToBuiltin (TypedBuiltinSized (SizeVar sizeIndex) typedBuiltin) (SizeValues sizes) f constant =
    unPairT . fmap SizeValues $ IntMap.alterF upd sizeIndex sizes where
        upd maySize = fmap Just . PairT $ applyToSizedBuiltin typedBuiltin maySize f constant
applyToBuiltin TypedBuiltinBool _ f constant = undefined

applySchemed
    :: TypeSchema a -> SizeValues -> (a -> b) -> Constant () -> Either ConstAppError (b, SizeValues)
applySchemed (TypeSchemaBuiltin a) sizeValues = applyToBuiltin a sizeValues
applySchemed (TypeSchemaArrow a b) sizeValues = undefined
applySchemed (TypeSchemaForall  k) sizeValues = undefined

wrapSizedConstant
    :: TypedBuiltinSized a -> Size -> a -> ConstAppResult
wrapSizedConstant TypedBuiltinInt  size int   = makeBuiltinInt  size int
wrapSizedConstant TypedBuiltinBS   size bs    = makeBuiltinBS   size bs
wrapSizedConstant TypedBuiltinSize size size' = makeBuiltinSize size size'

wrapConstant
    :: TypedBuiltin a -> SizeValues -> a -> ConstAppResult
wrapConstant (TypedBuiltinSized (SizeVar sizeIndex) typedSizedBuiltin) (SizeValues sizes) =
    wrapSizedConstant typedSizedBuiltin $ sizes IntMap.! sizeIndex
wrapConstant TypedBuiltinBool                                           _                 =
    makeBuiltinBool

applyTypedBuiltinName
    :: TypedBuiltinName a -> a -> [Constant ()] -> ConstAppResult
applyTypedBuiltinName (TypedBuiltinName _ schema) = go schema (SizeVar 0) (SizeValues mempty) where
    go :: TypeSchema a -> SizeVar -> SizeValues -> a -> [Constant ()] -> ConstAppResult
    go (TypeSchemaBuiltin builtin)       _       sizeValues y args = case args of
       [] -> wrapConstant builtin sizeValues y
       _  -> ConstAppError $ ExcessArgumentsConstAppErr args
    go (TypeSchemaArrow schemaA schemaB) sizeVar sizeValues f args = case args of
        []        -> ConstAppStuck
        x : args' -> case applySchemed schemaA sizeValues f x of
            Left err               -> ConstAppError err
            Right (y, sizeValues') -> go schemaB sizeVar sizeValues' y args'
    go (TypeSchemaForall k)              sizeVar sizeValues f args =
        go (k sizeVar) (succ sizeVar) sizeValues f args

sizeIntIntInt :: TypeSchema (Integer -> Integer -> Integer)
sizeIntIntInt =
    TypeSchemaForall $ \s ->
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt)

sizeIntIntBool :: TypeSchema (Integer -> Integer -> Bool)
sizeIntIntBool =
    TypeSchemaForall $ \s ->
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin TypedBuiltinBool

typedAddInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedAddInteger = TypedBuiltinName AddInteger sizeIntIntInt

typedSubtractInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedSubtractInteger = TypedBuiltinName SubtractInteger sizeIntIntInt

typedMultiplyInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedMultiplyInteger = TypedBuiltinName MultiplyInteger sizeIntIntInt

typedDivideInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedDivideInteger = TypedBuiltinName DivideInteger sizeIntIntInt

typedRemainderInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedRemainderInteger = TypedBuiltinName RemainderInteger sizeIntIntInt

typedLessThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedLessThanInteger = TypedBuiltinName LessThanInteger sizeIntIntBool

typedLessThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedLessThanEqInteger = TypedBuiltinName LessThanEqInteger sizeIntIntBool

typedGreaterThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedGreaterThanInteger = TypedBuiltinName GreaterThanInteger sizeIntIntBool

typedGreaterThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedGreaterThanEqInteger = TypedBuiltinName GreaterThanEqInteger sizeIntIntBool

typedEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedEqInteger = TypedBuiltinName EqInteger sizeIntIntBool

-- | Apply a `BuiltinName` to a list of arguments.
-- If the `BuiltinName` is saturated, return `Just` applied to the result of the computation.
-- Otherwise return `Nothing`.
-- Throw a `ConstAppException` if something goes wrong.
applyBuiltinName :: BuiltinName -> [Constant ()] -> ConstAppResult
applyBuiltinName AddInteger           = applyTypedBuiltinName typedAddInteger       (+)
applyBuiltinName SubtractInteger      = applyTypedBuiltinName typedSubtractInteger  (-)
applyBuiltinName MultiplyInteger      = applyTypedBuiltinName typedMultiplyInteger  (*)
applyBuiltinName DivideInteger        = applyTypedBuiltinName typedDivideInteger    div
applyBuiltinName RemainderInteger     = applyTypedBuiltinName typedRemainderInteger mod
applyBuiltinName LessThanInteger      = applyTypedBuiltinName typedLessThanInteger      (<)
applyBuiltinName LessThanEqInteger    = applyTypedBuiltinName typedLessThanEqInteger    (<=)
applyBuiltinName GreaterThanInteger   = applyTypedBuiltinName typedGreaterThanInteger   (>)
applyBuiltinName GreaterThanEqInteger = applyTypedBuiltinName typedGreaterThanEqInteger (>=)
applyBuiltinName EqInteger            = applyTypedBuiltinName typedEqInteger            (==)
applyBuiltinName IntToByteString      = undefined
applyBuiltinName Concatenate          = undefined
applyBuiltinName TakeByteString       = undefined
applyBuiltinName DropByteString       = undefined
applyBuiltinName ResizeByteString     = undefined
applyBuiltinName SHA2                 = undefined
applyBuiltinName SHA3                 = undefined
applyBuiltinName VerifySignature      = undefined
applyBuiltinName EqByteString         = undefined
applyBuiltinName TxHash               = undefined
applyBuiltinName BlockNum             = undefined
applyBuiltinName BlockTime            = undefined

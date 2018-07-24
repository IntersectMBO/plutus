{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Constant ( ConstAppRes(..)
                                    , ConstAppErr(..)
                                    , ConstAppExc(..)
                                    , IterApp(..)
                                    , viewPrimIterApp
                                    , applyBuiltinName
                                    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Type

import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.ByteString.Lazy as BSL

newtype PairT b f a = PairT
    { unPairT :: f (b, a)
    }

instance Functor f => Functor (PairT b f) where
    fmap f (PairT p) = PairT $ fmap (fmap f) p
    {-# INLINE fmap #-}

data ConstAppRes
    = ConstAppSuccess (Constant ())
    | ConstAppFailure

-- | The type of constant applications errors.
data ConstAppErr
    = SizeMismatchConstAppErr Size (Constant ())
    | forall a. IllTypedConstAppErr (TypedSizedBuiltin a) (Constant ())
    | ExcessArgumentsConstAppErr [Constant ()]

-- | The type of constant applications exceptions.
-- An attempt to apply a constant to inapproriate arguments results in this exception.
data ConstAppExc = ConstAppExc
    { _constAppExcErr   :: ConstAppErr
    , _constAppExcHead  :: BuiltinName
    , _constAppExcSpine :: [Constant ()]
    }

constAppErrString :: ConstAppErr -> String
constAppErrString (SizeMismatchConstAppErr seenSize constant)   = undefined
constAppErrString (IllTypedConstAppErr expType constant)        = undefined
constAppErrString (ExcessArgumentsConstAppErr excessArgs)       = undefined

-- TODO: we may not need those brackets.
instance Show ConstAppExc where
    show (ConstAppExc err name spine) = concat
        [ "An error occured while trying to reduce ("
        , prettyString name
        , spine >>= \arg -> " (" ++ prettyString arg ++ ")"
        , ") :"
        , constAppErrString err
        ]

instance Exception ConstAppExc

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

makeBuiltinInt :: Size -> Integer -> ConstAppRes
makeBuiltinInt size int
    | checkBoundsInt size int = ConstAppSuccess $ BuiltinInt () size int
    | otherwise               = ConstAppFailure

makeBuiltinBS :: Size -> BSL.ByteString -> ConstAppRes
makeBuiltinBS size bs
    | checkBoundsBS size bs = ConstAppSuccess $ BuiltinBS () size bs
    | otherwise             = ConstAppFailure

makeBuiltinSize :: Size -> Size -> ConstAppRes
makeBuiltinSize size size'
    | size == size' = ConstAppSuccess $ BuiltinSize () size
    | otherwise     = ConstAppFailure

infixr 9 `TypeSchemaArrow`

newtype SizeVar = SizeVar
    { unSizeVar :: Int
    }

newtype SizeValues = SizeValues
    { unSizeValues :: IntMap Size
    }

instance Enum SizeVar where
    toEnum = SizeVar
    fromEnum = unSizeVar

data TypedSizedBuiltin a where
    TypedBuiltinInt  :: TypedSizedBuiltin Integer
    TypedBuiltinBS   :: TypedSizedBuiltin BSL.ByteString
    TypedBuiltinSize :: TypedSizedBuiltin Size

data TypedBuiltin a where
    TypedSizedBuiltin :: SizeVar -> TypedSizedBuiltin a -> TypedBuiltin a

data TypeSchema a where
    TypeSchemaBuiltin :: TypedBuiltin a -> TypeSchema a
    TypeSchemaArrow   :: TypeSchema a -> TypeSchema b -> TypeSchema (a -> b)
    TypeSchemaForall  :: (SizeVar -> TypeSchema a) -> TypeSchema a

data TypedBuiltinName a = TypedBuiltinName BuiltinName (TypeSchema a)

checkBuiltinSize :: Maybe Size -> Size -> Constant () -> b -> Either ConstAppErr (b, Size)
checkBuiltinSize (Just size) size' constant _ | size /= size' =
    Left $ SizeMismatchConstAppErr size constant
checkBuiltinSize  _          size' _        y = Right (y, size')

applyToSizedBuiltin
    :: TypedSizedBuiltin a -> Maybe Size -> (a -> b) -> Constant () -> Either ConstAppErr (b, Size)
applyToSizedBuiltin TypedBuiltinInt  maySize f constant@(BuiltinInt  () size' int) =
    checkBuiltinSize maySize size' constant (f int)
applyToSizedBuiltin TypedBuiltinBS   maySize f constant@(BuiltinBS   () size' bs ) =
    checkBuiltinSize maySize size' constant (f bs)
applyToSizedBuiltin TypedBuiltinSize maySize f constant@(BuiltinSize () size'    ) =
    checkBuiltinSize maySize size' constant (f size')
applyToSizedBuiltin typedBuiltin     _       _ constant                            =
    Left $ IllTypedConstAppErr typedBuiltin constant

applyToBuiltin
    :: TypedBuiltin a -> SizeValues -> (a -> b) -> Constant () -> Either ConstAppErr (b, SizeValues)
applyToBuiltin (TypedSizedBuiltin (SizeVar sizeIndex) typedBuiltin) (SizeValues sizes) f constant =
    unPairT . fmap SizeValues $ IntMap.alterF upd sizeIndex sizes where
        upd maySize = fmap Just . PairT $ applyToSizedBuiltin typedBuiltin maySize f constant

applySchemed
    :: TypeSchema a -> SizeValues -> (a -> b) -> Constant () -> Either ConstAppErr (b, SizeValues)
applySchemed (TypeSchemaBuiltin a) sizeValues = applyToBuiltin a sizeValues
applySchemed (TypeSchemaArrow a b) sizeValues = undefined
applySchemed (TypeSchemaForall  k) sizeValues = undefined

wrapSizedConstant
    :: TypedSizedBuiltin a -> Size -> a -> ConstAppRes
wrapSizedConstant TypedBuiltinInt  size int   = makeBuiltinInt  size int
wrapSizedConstant TypedBuiltinBS   size bs    = makeBuiltinBS   size bs
wrapSizedConstant TypedBuiltinSize size size' = makeBuiltinSize size size'

wrapConstant
    :: TypedBuiltin a -> SizeValues -> a -> ConstAppRes
wrapConstant (TypedSizedBuiltin (SizeVar sizeIndex) typedSizedBuiltin) (SizeValues sizes) =
    wrapSizedConstant typedSizedBuiltin $ sizes IntMap.! sizeIndex

applyTypedBuiltinName
    :: TypedBuiltinName a -> a -> [Constant ()] -> Either ConstAppErr (Maybe ConstAppRes)
applyTypedBuiltinName (TypedBuiltinName _ schema) = go schema (SizeVar 0) (SizeValues mempty) where
    go
        :: TypeSchema a
        -> SizeVar
        -> SizeValues
        -> a
        -> [Constant ()]
        -> Either ConstAppErr (Maybe ConstAppRes)
    go (TypeSchemaBuiltin builtin)       _       sizeValues y args =
        case args of
            [] -> Right . Just $ wrapConstant builtin sizeValues y
            _  -> Left $ ExcessArgumentsConstAppErr args
    go (TypeSchemaArrow schemaA schemaB) sizeVar sizeValues f args =
        case args of
            []        -> Right Nothing
            x : args' -> do
                (y, sizeValues') <- applySchemed schemaA sizeValues f x
                go schemaB sizeVar sizeValues' y args'
    go (TypeSchemaForall k)              sizeVar sizeValues f args =
        go (k sizeVar) (succ sizeVar) sizeValues f args

sizeIntIntInt :: TypeSchema (Integer -> Integer -> Integer)
sizeIntIntInt =
    TypeSchemaForall $ \s ->
        TypeSchemaBuiltin (TypedSizedBuiltin s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedSizedBuiltin s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedSizedBuiltin s TypedBuiltinInt)

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

-- | Apply a `BuiltinName` to a list of arguments.
-- If the `BuiltinName` is saturated, return `Just` applied to the result of the computation.
-- Otherwise return `Nothing`.
-- Throw a `ConstAppExc` if something goes wrong.
applyBuiltinNameSafe :: BuiltinName -> [Constant ()] -> Either ConstAppErr (Maybe ConstAppRes)
applyBuiltinNameSafe AddInteger           = applyTypedBuiltinName typedAddInteger       (+)
applyBuiltinNameSafe SubtractInteger      = applyTypedBuiltinName typedSubtractInteger  (-)
applyBuiltinNameSafe MultiplyInteger      = applyTypedBuiltinName typedMultiplyInteger  (*)
applyBuiltinNameSafe DivideInteger        = applyTypedBuiltinName typedDivideInteger    div
applyBuiltinNameSafe RemainderInteger     = applyTypedBuiltinName typedRemainderInteger mod
applyBuiltinNameSafe LessThanInteger      = undefined
applyBuiltinNameSafe LessThanEqInteger    = undefined
applyBuiltinNameSafe GreaterThanInteger   = undefined
applyBuiltinNameSafe GreaterThanEqInteger = undefined
applyBuiltinNameSafe EqInteger            = undefined
applyBuiltinNameSafe IntToByteString      = undefined
applyBuiltinNameSafe Concatenate          = undefined
applyBuiltinNameSafe TakeByteString       = undefined
applyBuiltinNameSafe DropByteString       = undefined
applyBuiltinNameSafe ResizeByteString     = undefined
applyBuiltinNameSafe SHA2                 = undefined
applyBuiltinNameSafe SHA3                 = undefined
applyBuiltinNameSafe VerifySignature      = undefined
applyBuiltinNameSafe EqByteString         = undefined
applyBuiltinNameSafe TxHash               = undefined
applyBuiltinNameSafe BlockNum             = undefined
applyBuiltinNameSafe BlockTime            = undefined

applyBuiltinName :: BuiltinName -> [Constant ()] -> Maybe ConstAppRes
applyBuiltinName name args =
    either (\err -> throw $ ConstAppExc err name args) id $
        applyBuiltinNameSafe name args

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

import           Data.List
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.ByteString.Lazy as BSL

data ConstAppRes = ConstAppSuccess (Constant ())
                 | ConstAppFailure

-- | The type of constant applications errors.
data ConstAppErr = SizeMismatchAppErr (Constant ()) (Constant ())
                 | IllTypedAppErr (Constant ())
                 | ExcessArgumentsAppErr [Constant ()]
                 | NonSingletonSizeAppErr Natural Natural

-- | The type of constant applications exceptions.
-- An attempt to apply a constant to inapproriate arguments results in this exception.
data ConstAppExc = ConstAppExc
    { _constAppExcErr :: ConstAppErr
    , _constAppExcHead  :: BuiltinName
    , _constAppExcSpine :: [Constant ()]
    }

instance Show ConstAppExc where
    show = undefined
    -- show (ConstAppExc err) = Text.unpack err

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

data TypedBuiltin a where
    TypedBuiltinInt  :: SizeVar -> TypedBuiltin Integer
    TypedBuiltinBS   :: SizeVar -> TypedBuiltin BSL.ByteString
    TypedBuiltinSize :: SizeVar -> TypedBuiltin Size

data TypeSchema a where
    TypeSchemaBuiltin :: TypedBuiltin a -> TypeSchema a
    TypeSchemaArrow   :: TypeSchema a -> TypeSchema b -> TypeSchema (a -> b)
    TypeSchemaForall  :: (SizeVar -> TypeSchema a) -> TypeSchema a

data TypedBuiltinName a = TypedBuiltinName BuiltinName (TypeSchema a)

-- throwAppExc $ SizeMismatchAppErr a1 a2
-- throwAppExc $ IllTypedAppErr a1
applySchemed
    :: TypeSchema a -> SizeValues -> (a -> b) -> Constant () -> Either ConstAppErr (b, SizeValues)
applySchemed (TypeSchemaBuiltin a) _ f = undefined
applySchemed (TypeSchemaArrow a b) _ f = undefined
applySchemed (TypeSchemaForall  k) _ f = undefined

wrapConstant
    :: SizeValues -> TypedBuiltin a -> a -> Either ConstAppErr ConstAppRes
wrapConstant (SizeValues sizes) (TypedBuiltinInt  (SizeVar sizeIndex)) int  =
    Right $ makeBuiltinInt (sizes IntMap.! sizeIndex) int
wrapConstant (SizeValues sizes) (TypedBuiltinBS   (SizeVar sizeIndex)) str  =
    Right $ makeBuiltinBS  (sizes IntMap.! sizeIndex) str
wrapConstant (SizeValues sizes) (TypedBuiltinSize (SizeVar sizeIndex)) size
    | size == size' = Right . ConstAppSuccess $ BuiltinSize () size
    | otherwise     = Left $ NonSingletonSizeAppErr size size'
    where size' = sizes IntMap.! sizeIndex

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
            [] -> Just <$> wrapConstant sizeValues builtin y
            _  -> Left $ ExcessArgumentsAppErr args
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
        TypeSchemaBuiltin (TypedBuiltinInt s) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedBuiltinInt s) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedBuiltinInt s)

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
applyBuiltinName name args
    = either (\err -> throw $ ConstAppExc err name args) id
    $ applyBuiltinNameSafe name args

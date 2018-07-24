{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Constant ( ConstantApplicationResult(..)
                                    , ConstantApplicationError(..)
                                    , ConstantApplicationException(..)
                                    , IteratedApplication(..)
                                    , viewPrimIteratedApplication
                                    , applyBuiltinName
                                    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Type

import           Data.List
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.ByteString.Lazy as BSL

data ConstantApplicationResult = ConstantApplicationSuccess (Constant ())
                               | ConstantApplicationFailure

data ConstantApplicationError = SizeMismatchApplicationError (Constant ()) (Constant ())
                              | IllTypedApplicationError (Constant ())
                              | ExcessArgumentsApplicationError [Constant ()]
                              | NonSingletonSizeApplicationError Natural Natural

-- | An attempt to apply a constant to inapproriate arguments results in this exception.
data ConstantApplicationException = ConstantApplicationException
    { _constantApplicationExceptionError :: ConstantApplicationError
    , _constantApplicationExceptionHead  :: BuiltinName
    , _constantApplicationExceptionSpine :: [Constant ()]
    }

instance Show ConstantApplicationException where
    show = undefined
    -- show (ConstantApplicationException err) = Text.unpack err

instance Exception ConstantApplicationException

-- | A function (called "head") applied to a list of arguments (called "spine").
data IteratedApplication head arg = IteratedApplication
    { _iteratedApplicationHead  :: head
    , _iteratedApplicationSpine :: [arg]
    }

type TermIteratedApplication tyname name a =
    IteratedApplication (Term tyname name a) (Term tyname name a)

type PrimIteratedApplication =
    IteratedApplication BuiltinName (Constant ())

-- | View a `Constant` as a `BuiltinName`.
viewBuiltinName :: Constant a -> Maybe BuiltinName
viewBuiltinName (BuiltinName _ name) = Just name
viewBuiltinName _                    = Nothing

-- | View a `Term` as a `Constant`.
viewConstant :: Term tyname name a -> Maybe (Constant a)
viewConstant (Constant _ constant) = Just constant
viewConstant _                     = Nothing

-- | View a `Term` as an `IteratedApplication`.
viewTermIteratedApplication :: Term tyname name a -> Maybe (TermIteratedApplication tyname name a)
viewTermIteratedApplication term@Apply{} = Just $ go [] term where
    go args (Apply _ fun arg) = go (undefined arg : args) fun
    go args  fun              = IteratedApplication fun args
viewTermIteratedApplication _            = Nothing

-- | View a `Term` as an iterated application of a `BuiltinName` to a list of `Constants`.
viewPrimIteratedApplication :: Term tyname name () -> Maybe PrimIteratedApplication
viewPrimIteratedApplication term = do
    IteratedApplication termHead termSpine <- viewTermIteratedApplication term
    headName <- viewConstant termHead >>= viewBuiltinName
    spine <- traverse viewConstant termSpine
    Just $ IteratedApplication headName spine

type Size = Natural

checkBoundsInt :: Size -> Integer -> Bool
checkBoundsInt s i = -2 ^ p <= i && i < 2 ^ p where
  p = 8 * fromIntegral s - 1 :: Int

checkBoundsBS :: Size -> BSL.ByteString -> Bool
checkBoundsBS = undefined

makeBuiltinInt :: Size -> Integer -> ConstantApplicationResult
makeBuiltinInt size int
    | checkBoundsInt size int = ConstantApplicationSuccess $ BuiltinInt () size int
    | otherwise               = ConstantApplicationFailure

makeBuiltinBS :: Size -> BSL.ByteString -> ConstantApplicationResult
makeBuiltinBS size bs
    | checkBoundsBS size bs = ConstantApplicationSuccess $ BuiltinBS () size bs
    | otherwise             = ConstantApplicationFailure

infixr 9 `SchemaArrow`

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
    SchemaBuiltin :: TypedBuiltin a -> TypeSchema a
    SchemaArrow   :: TypeSchema a -> TypeSchema b -> TypeSchema (a -> b)
    SchemaForall  :: (SizeVar -> TypeSchema a) -> TypeSchema a

data TypedBuiltinName a = TypedBuiltinName BuiltinName (TypeSchema a)

sizeIntIntInt :: TypeSchema (Integer -> Integer -> Integer)
sizeIntIntInt =
    SchemaForall $ \s ->
        SchemaBuiltin (TypedBuiltinInt s) `SchemaArrow`
        SchemaBuiltin (TypedBuiltinInt s) `SchemaArrow`
        SchemaBuiltin (TypedBuiltinInt s)

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

-- throwAppExc $ SizeMismatchApplicationError a1 a2
-- throwAppExc $ IllTypedApplicationError a1
applySchemed :: TypeSchema a -> SizeValues -> (a -> b) -> Constant () -> (b, SizeValues)
applySchemed = undefined

wrapConstant
    :: (forall c. ConstantApplicationError -> c)
    -> SizeValues -> TypedBuiltin a -> a -> ConstantApplicationResult
wrapConstant _           (SizeValues sizes) (TypedBuiltinInt  (SizeVar sizeIndex)) int  =
    makeBuiltinInt (sizes IntMap.! sizeIndex) int
wrapConstant _           (SizeValues sizes) (TypedBuiltinBS   (SizeVar sizeIndex)) str  =
    makeBuiltinBS  (sizes IntMap.! sizeIndex) str
wrapConstant throwAppErr (SizeValues sizes) (TypedBuiltinSize (SizeVar sizeIndex)) size
    | size == size' = ConstantApplicationSuccess $ BuiltinSize () size
    | otherwise     = throwAppErr $ NonSingletonSizeApplicationError size size'
    where size' = sizes IntMap.! sizeIndex

applyTypedBuiltinName
    :: TypedBuiltinName a -> a -> [Constant ()] -> Maybe ConstantApplicationResult
applyTypedBuiltinName (TypedBuiltinName name schema) f0 args0 =
    go schema (SizeVar 0) (SizeValues mempty) f0 args0 where
        throwAppErr :: ConstantApplicationError -> c
        throwAppErr err = throw $ ConstantApplicationException err name args0

        go :: TypeSchema a -> SizeVar -> SizeValues -> a -> [Constant ()] -> Maybe ConstantApplicationResult
        go (SchemaBuiltin builtin)       _       sizeValues y args =
            case args of
                [] -> Just $ wrapConstant throwAppErr sizeValues builtin y
                _  -> throwAppErr $ ExcessArgumentsApplicationError args
        go (SchemaArrow schemaA schemaB) sizeVar sizeValues f args = do
            (x, args') <- uncons args
            let (y, sizeValues') = applySchemed schemaA sizeValues f x
            go schemaB sizeVar sizeValues' y args'
        go (SchemaForall k)              sizeVar sizeValues f args =
            go (k sizeVar) (succ sizeVar) sizeValues f args

-- | Apply a `BuiltinName` to a list of arguments.
-- If the `BuiltinName` is saturated, return `Just` applied to the result of the computation.
-- Otherwise return `Nothing`.
-- Throw a `ConstantApplicationException` if something goes wrong.
applyBuiltinName :: BuiltinName -> [Constant ()] -> Maybe ConstantApplicationResult
applyBuiltinName AddInteger           = applyTypedBuiltinName typedAddInteger       (+)
applyBuiltinName SubtractInteger      = applyTypedBuiltinName typedSubtractInteger  (-)
applyBuiltinName MultiplyInteger      = applyTypedBuiltinName typedMultiplyInteger  (*)
applyBuiltinName DivideInteger        = applyTypedBuiltinName typedDivideInteger    div
applyBuiltinName RemainderInteger     = applyTypedBuiltinName typedRemainderInteger mod
applyBuiltinName LessThanInteger      = undefined
applyBuiltinName LessThanEqInteger    = undefined
applyBuiltinName GreaterThanInteger   = undefined
applyBuiltinName GreaterThanEqInteger = undefined
applyBuiltinName EqInteger            = undefined
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

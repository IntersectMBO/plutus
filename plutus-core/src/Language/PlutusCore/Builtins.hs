{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Builtins where

import           Language.PlutusCore.Constant.Meaning
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Universe

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import           Control.DeepSeq
import           Crypto
import qualified Data.ByteString                                            as BS
import qualified Data.ByteString.Hash                                       as Hash
import           Data.Ix
import           Data.Text.Prettyprint.Doc
import           Debug.Trace                                                (traceIO)
import           GHC.Generics
import           System.IO.Unsafe

-- TODO: I think we should have the following structure:
--
-- Language.PlutusCore.Default.Universe
-- Language.PlutusCore.Default.Builtins
--
-- and
--
-- Language.PlutusCore.Default
--
-- reexporting stuff from these two.

-- | Default built-in functions.
data DefaultFun
    = AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | LessThanInteger
    | LessThanEqInteger
    | GreaterThanInteger
    | GreaterThanEqInteger
    | EqInteger
    | Concatenate
    | TakeByteString
    | DropByteString
    | SHA2
    | SHA3
    | VerifySignature
    | EqByteString
    | LtByteString
    | GtByteString
    | IfThenElse
    | CharToString
    | Append
    | Trace
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Hashable, Ix)

-- TODO: do we really want function names to be pretty-printed differently to what they are named as
-- constructors of 'DefaultFun'?
instance Pretty DefaultFun where
    pretty AddInteger           = "addInteger"
    pretty SubtractInteger      = "subtractInteger"
    pretty MultiplyInteger      = "multiplyInteger"
    pretty DivideInteger        = "divideInteger"
    pretty QuotientInteger      = "quotientInteger"
    pretty ModInteger           = "modInteger"
    pretty RemainderInteger     = "remainderInteger"
    pretty LessThanInteger      = "lessThanInteger"
    pretty LessThanEqInteger    = "lessThanEqualsInteger"
    pretty GreaterThanInteger   = "greaterThanInteger"
    pretty GreaterThanEqInteger = "greaterThanEqualsInteger"
    pretty EqInteger            = "equalsInteger"
    pretty Concatenate          = "concatenate"
    pretty TakeByteString       = "takeByteString"
    pretty DropByteString       = "dropByteString"
    pretty EqByteString         = "equalsByteString"
    pretty LtByteString         = "lessThanByteString"
    pretty GtByteString         = "greaterThanByteString"
    pretty SHA2                 = "sha2_256"
    pretty SHA3                 = "sha3_256"
    pretty VerifySignature      = "verifySignature"
    pretty IfThenElse           = "ifThenElse"
    pretty CharToString         = "charToString"
    pretty Append               = "append"
    pretty Trace                = "trace"

instance ExMemoryUsage DefaultFun where
    memoryUsage _ = 1

newtype DefaultFunDyn = DefaultFunDyn
    { defaultFunDynTrace :: String -> IO ()
    }

instance Semigroup DefaultFunDyn where
    DefaultFunDyn trace1 <> DefaultFunDyn trace2 = DefaultFunDyn $ \str -> trace1 str `seq` trace2 str

instance Monoid DefaultFunDyn where
    mempty = DefaultFunDyn traceIO

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

integerToInt :: Integer -> Int
integerToInt = fromIntegral

defBuiltinsRuntime :: HasConstantIn DefaultUni term => BuiltinsRuntime DefaultFun term
defBuiltinsRuntime = toBuiltinsRuntime mempty defaultCostModel

instance (GShow uni, GEq uni, DefaultUni <: uni) => ToBuiltinMeaning uni DefaultFun where
    type DynamicPart uni DefaultFun = DefaultFunDyn
    type CostingPart uni DefaultFun = CostModel
    toBuiltinMeaning AddInteger =
        toStaticBuiltinMeaning
            ((+) @Integer)
            (runCostingFunTwoArguments . paramAddInteger)
    toBuiltinMeaning SubtractInteger =
        toStaticBuiltinMeaning
            ((-) @Integer)
            (runCostingFunTwoArguments . paramSubtractInteger)
    toBuiltinMeaning MultiplyInteger =
        toStaticBuiltinMeaning
            ((*) @Integer)
            (runCostingFunTwoArguments . paramMultiplyInteger)
    toBuiltinMeaning DivideInteger =
        toStaticBuiltinMeaning
            (nonZeroArg div)
            (runCostingFunTwoArguments . paramDivideInteger)
    toBuiltinMeaning QuotientInteger =
        toStaticBuiltinMeaning
            (nonZeroArg quot)
            (runCostingFunTwoArguments . paramQuotientInteger)
    toBuiltinMeaning RemainderInteger =
        toStaticBuiltinMeaning
            (nonZeroArg rem)
            (runCostingFunTwoArguments . paramRemainderInteger)
    toBuiltinMeaning ModInteger =
        toStaticBuiltinMeaning
            (nonZeroArg mod)
            (runCostingFunTwoArguments . paramModInteger)
    toBuiltinMeaning LessThanInteger =
        toStaticBuiltinMeaning
            ((<) @Integer)
            (runCostingFunTwoArguments . paramLessThanInteger)
    toBuiltinMeaning LessThanEqInteger =
        toStaticBuiltinMeaning
            ((<=) @Integer)
            (runCostingFunTwoArguments . paramLessThanEqInteger)
    toBuiltinMeaning GreaterThanInteger =
        toStaticBuiltinMeaning
            ((>) @Integer)
            (runCostingFunTwoArguments . paramGreaterThanInteger)
    toBuiltinMeaning GreaterThanEqInteger =
        toStaticBuiltinMeaning
            ((>=) @Integer)
            (runCostingFunTwoArguments . paramGreaterThanEqInteger)
    toBuiltinMeaning EqInteger =
        toStaticBuiltinMeaning
            ((==) @Integer)
            (runCostingFunTwoArguments . paramEqInteger)
    toBuiltinMeaning Concatenate =
        toStaticBuiltinMeaning
            BS.append
            (runCostingFunTwoArguments . paramConcatenate)
    toBuiltinMeaning TakeByteString =
        toStaticBuiltinMeaning
            (BS.take . integerToInt)
            (runCostingFunTwoArguments . paramTakeByteString)
    toBuiltinMeaning DropByteString =
        toStaticBuiltinMeaning
            (BS.drop . integerToInt)
            (runCostingFunTwoArguments . paramDropByteString)
    toBuiltinMeaning SHA2 =
        toStaticBuiltinMeaning
            Hash.sha2
            (runCostingFunOneArgument . paramSHA2)
    toBuiltinMeaning SHA3 =
        toStaticBuiltinMeaning
            Hash.sha3
            (runCostingFunOneArgument . paramSHA3)
    toBuiltinMeaning VerifySignature =
        toStaticBuiltinMeaning
            (verifySignature @EvaluationResult)
            (runCostingFunThreeArguments . paramVerifySignature)
    toBuiltinMeaning EqByteString =
        toStaticBuiltinMeaning
            ((==) @BS.ByteString)
            (runCostingFunTwoArguments . paramEqByteString)
    toBuiltinMeaning LtByteString =
        toStaticBuiltinMeaning
            ((<) @BS.ByteString)
            (runCostingFunTwoArguments . paramLtByteString)
    toBuiltinMeaning GtByteString =
        toStaticBuiltinMeaning
            ((>) @BS.ByteString)
            (runCostingFunTwoArguments . paramGtByteString)
    toBuiltinMeaning IfThenElse =
        toStaticBuiltinMeaning
            ((\b x y -> if b then x else y) :: a ~ Opaque term (TyVarRep "a" 0) => Bool -> a -> a -> a)
            (runCostingFunThreeArguments . paramIfThenElse)
    toBuiltinMeaning CharToString =
        toStaticBuiltinMeaning
            (pure :: Char -> String)
            mempty  -- TODO: budget.
    toBuiltinMeaning Append =
        toStaticBuiltinMeaning
            ((++) :: String -> String -> String)
            mempty  -- TODO: budget.
    toBuiltinMeaning Trace =
        toDynamicBuiltinMeaning
            (\env -> unsafePerformIO . defaultFunDynTrace env)
            mempty  -- TODO: budget.

-- See Note [Stable encoding of PLC]
instance Serialise DefaultFun where
    encode = encodeWord . \case
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
              IfThenElse           -> 21
              CharToString         -> 22
              Append               -> 23
              Trace                -> 24

    decode = go =<< decodeWord
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
              go 21 = pure IfThenElse
              go 22 = pure CharToString
              go 23 = pure Append
              go 24 = pure Trace
              go _  = fail "Failed to decode BuiltinName"

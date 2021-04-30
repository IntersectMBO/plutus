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

module PlutusCore.Default.Builtins where

import           PlutusCore.Constant.Dynamic.Emit
import           PlutusCore.Constant.Meaning
import           PlutusCore.Constant.Typed
import           PlutusCore.Default.Universe
import           PlutusCore.Evaluation.Machine.ExBudgeting
import           PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.Evaluation.Result
import           PlutusCore.Pretty
import           PlutusCore.Universe

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import           Control.DeepSeq
import           Crypto
import qualified Data.ByteString                                   as BS
import qualified Data.ByteString.Hash                              as Hash
import           Data.Ix
import           Data.Word                                         (Word8)
import           Flat
import           Flat.Decoder
import           Flat.Encoder                                      as Flat

-- For @n >= 24@, CBOR needs two bytes instead of one to encode @n@, so we want the commonest
-- builtins at the front.
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
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Hashable, Ix, PrettyBy PrettyConfigPlc)

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

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

defBuiltinsRuntime :: HasConstantIn DefaultUni term => BuiltinsRuntime DefaultFun term
defBuiltinsRuntime = toBuiltinsRuntime defaultCostModel

instance (GShow uni, GEq uni, DefaultUni <: uni) => ToBuiltinMeaning uni DefaultFun where
    type CostingPart uni DefaultFun = CostModel
    toBuiltinMeaning AddInteger =
        makeBuiltinMeaning
            ((+) @Integer)
            (runCostingFunTwoArguments . paramAddInteger)
    toBuiltinMeaning SubtractInteger =
        makeBuiltinMeaning
            ((-) @Integer)
            (runCostingFunTwoArguments . paramSubtractInteger)
    toBuiltinMeaning MultiplyInteger =
        makeBuiltinMeaning
            ((*) @Integer)
            (runCostingFunTwoArguments . paramMultiplyInteger)
    toBuiltinMeaning DivideInteger =
        makeBuiltinMeaning
            (nonZeroArg div)
            (runCostingFunTwoArguments . paramDivideInteger)
    toBuiltinMeaning QuotientInteger =
        makeBuiltinMeaning
            (nonZeroArg quot)
            (runCostingFunTwoArguments . paramQuotientInteger)
    toBuiltinMeaning RemainderInteger =
        makeBuiltinMeaning
            (nonZeroArg rem)
            (runCostingFunTwoArguments . paramRemainderInteger)
    toBuiltinMeaning ModInteger =
        makeBuiltinMeaning
            (nonZeroArg mod)
            (runCostingFunTwoArguments . paramModInteger)
    toBuiltinMeaning LessThanInteger =
        makeBuiltinMeaning
            ((<) @Integer)
            (runCostingFunTwoArguments . paramLessThanInteger)
    toBuiltinMeaning LessThanEqInteger =
        makeBuiltinMeaning
            ((<=) @Integer)
            (runCostingFunTwoArguments . paramLessThanEqInteger)
    toBuiltinMeaning GreaterThanInteger =
        makeBuiltinMeaning
            ((>) @Integer)
            (runCostingFunTwoArguments . paramGreaterThanInteger)
    toBuiltinMeaning GreaterThanEqInteger =
        makeBuiltinMeaning
            ((>=) @Integer)
            (runCostingFunTwoArguments . paramGreaterThanEqInteger)
    toBuiltinMeaning EqInteger =
        makeBuiltinMeaning
            ((==) @Integer)
            (runCostingFunTwoArguments . paramEqInteger)
    toBuiltinMeaning Concatenate =
        makeBuiltinMeaning
            BS.append
            (runCostingFunTwoArguments . paramConcatenate)
    toBuiltinMeaning TakeByteString =
        makeBuiltinMeaning
            BS.take
            (runCostingFunTwoArguments . paramTakeByteString)
    toBuiltinMeaning DropByteString =
        makeBuiltinMeaning
            BS.drop
            (runCostingFunTwoArguments . paramDropByteString)
    toBuiltinMeaning SHA2 =
        makeBuiltinMeaning
            Hash.sha2
            (runCostingFunOneArgument . paramSHA2)
    toBuiltinMeaning SHA3 =
        makeBuiltinMeaning
            Hash.sha3
            (runCostingFunOneArgument . paramSHA3)
    toBuiltinMeaning VerifySignature =
        makeBuiltinMeaning
            (verifySignature @EvaluationResult)
            (runCostingFunThreeArguments . paramVerifySignature)
    toBuiltinMeaning EqByteString =
        makeBuiltinMeaning
            ((==) @BS.ByteString)
            (runCostingFunTwoArguments . paramEqByteString)
    toBuiltinMeaning LtByteString =
        makeBuiltinMeaning
            ((<) @BS.ByteString)
            (runCostingFunTwoArguments . paramLtByteString)
    toBuiltinMeaning GtByteString =
        makeBuiltinMeaning
            ((>) @BS.ByteString)
            (runCostingFunTwoArguments . paramGtByteString)
    toBuiltinMeaning IfThenElse =
       makeBuiltinMeaning
            (\b x y -> if b then x else y)
            (runCostingFunThreeArguments . paramIfThenElse)
    toBuiltinMeaning CharToString =
        makeBuiltinMeaning
            (pure :: Char -> String)
            mempty  -- TODO: budget.
    toBuiltinMeaning Append =
        makeBuiltinMeaning
            ((++) :: String -> String -> String)
            mempty  -- TODO: budget.
    toBuiltinMeaning Trace =
        makeBuiltinMeaning
            (emit :: String -> Emitter ())
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

-- It's set deliberately to give us "extra room" in the binary format to add things without running
-- out of space for tags (expanding the space would change the binary format for people who're
-- implementing it manually). So we have to set it manually.
-- | Using 5 bits to encode builtin tags.
builtinTagWidth :: NumBits
builtinTagWidth = 5

encodeBuiltin :: Word8 -> Flat.Encoding
encodeBuiltin = eBits builtinTagWidth

decodeBuiltin :: Get Word8
decodeBuiltin = dBEBits8 builtinTagWidth

-- See Note [Stable encoding of PLC]
instance Flat DefaultFun where
    encode = encodeBuiltin . \case
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

    decode = go =<< decodeBuiltin
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

    size _ n = n + builtinTagWidth

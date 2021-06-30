{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Default.Builtins where

import           PlutusCore.Constant
import           PlutusCore.Data
import           PlutusCore.Default.Universe
import           PlutusCore.Evaluation.Machine.BuiltinCostModel
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.Evaluation.Result
import           PlutusCore.Pretty

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import           Control.DeepSeq
import           Crypto
import qualified Data.ByteString                                as BS
import qualified Data.ByteString.Char8                          as BSC
import qualified Data.ByteString.Hash                           as Hash
import           Data.Char
import           Data.Ix
import           Data.Word                                      (Word8)
import           Flat
import           Flat.Decoder
import           Flat.Encoder                                   as Flat

-- See Note [Pattern matching on built-in types].
-- TODO: should we have the commonest builtins at the front to have more compact encoding?
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
    | EqualsString
    | EncodeUtf8
    | DecodeUtf8
    | Trace
    | FstPair
    | SndPair
    | NullList
    | HeadList
    | TailList
    | ConstrData
    | MapData
    | ListData
    | IData
    | BData
    | UnConstrData
    | UnMapData
    | UnListData
    | UnIData
    | UnBData
    | EqualsData
    -- It is convenient to have a "choosing" function for a data type that has more than two
    -- constructors to get pattern matching over it and we may end up having multiple such data
    -- types, hence we include the name of the data type as a suffix.
    | ChooseData
    -- TODO. These are only used for costing calibration and shouldn't be included in the defaults.
    | Nop1
    | Nop2
    | Nop3
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Hashable, Ix, PrettyBy PrettyConfigPlc)

instance Pretty DefaultFun where
    pretty fun = case show fun of
        ""    -> error "Panic: 'show' is not supposed to return an empty string"
        c : s -> pretty $ toLower c : s

instance ExMemoryUsage DefaultFun where
    memoryUsage _ = 1

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

instance uni ~ DefaultUni => ToBuiltinMeaning uni DefaultFun where
    type CostingPart uni DefaultFun = BuiltinCostModel
    toBuiltinMeaning
        :: forall term. HasConstantIn uni term
        => DefaultFun -> BuiltinMeaning term BuiltinCostModel
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
    toBuiltinMeaning EqualsString =
        makeBuiltinMeaning
            ((==) @String)
            mempty  -- TODO: budget.
    toBuiltinMeaning EncodeUtf8 =
        makeBuiltinMeaning
            (BSC.pack :: String -> BS.ByteString)
            mempty  -- TODO: budget.
    toBuiltinMeaning DecodeUtf8 =
        makeBuiltinMeaning
            (BSC.unpack :: BS.ByteString -> String)
            mempty  -- TODO: budget.
    toBuiltinMeaning Trace =
        makeBuiltinMeaning
            (emit :: String -> Emitter ())
            mempty  -- TODO: budget.
    toBuiltinMeaning Nop1 =
        makeBuiltinMeaning
            @(Integer -> ())
            mempty
            mempty
    toBuiltinMeaning Nop2 =
        makeBuiltinMeaning
            @(Integer -> Integer -> ())
            mempty
            mempty
    toBuiltinMeaning Nop3 =
        makeBuiltinMeaning
            @(Integer -> Integer -> Integer -> ())
            mempty
            mempty
    toBuiltinMeaning FstPair = makeBuiltinMeaning fstPlc mempty where
        fstPlc :: SomeConstantOf uni (,) '[a, b] -> Opaque term a
        fstPlc (SomeConstantOfArg uniA (SomeConstantOfArg _ (SomeConstantOfRes _ (x, _)))) =
            Opaque . fromConstant . Some $ ValueOf uniA x
    toBuiltinMeaning SndPair = makeBuiltinMeaning sndPlc mempty where
        sndPlc :: SomeConstantOf uni (,) '[a, b] -> Opaque term b
        sndPlc (SomeConstantOfArg _ (SomeConstantOfArg uniB (SomeConstantOfRes _ (_, y)))) =
            Opaque . fromConstant . Some $ ValueOf uniB y
    toBuiltinMeaning NullList = makeBuiltinMeaning nullPlc mempty where
        nullPlc :: SomeConstantOf uni [] '[a] -> Bool
        nullPlc (SomeConstantOfArg _ (SomeConstantOfRes _ xs)) = null xs
    toBuiltinMeaning HeadList = makeBuiltinMeaning headPlc mempty where
        headPlc :: SomeConstantOf uni [] '[a] -> EvaluationResult (Opaque term a)
        headPlc (SomeConstantOfArg uniA (SomeConstantOfRes _ xs)) = case xs of
            x : _ -> EvaluationSuccess . Opaque . fromConstant $ someValueOf uniA x
            _     -> EvaluationFailure
    toBuiltinMeaning TailList = makeBuiltinMeaning tailPlc mempty where
        tailPlc :: SomeConstantOf uni [] '[a] -> EvaluationResult (SomeConstantOf uni [] '[a])
        tailPlc (SomeConstantOfArg uniA (SomeConstantOfRes uniListA xs)) = case xs of
            _ : xs' -> EvaluationSuccess . SomeConstantOfArg uniA $ SomeConstantOfRes uniListA xs'
            _       -> EvaluationFailure
    toBuiltinMeaning ConstrData =
        makeBuiltinMeaning
            Constr
            mempty
    toBuiltinMeaning MapData =
        makeBuiltinMeaning
            Map
            mempty
    toBuiltinMeaning ListData =
        makeBuiltinMeaning
            List
            mempty
    toBuiltinMeaning IData =
        makeBuiltinMeaning
            I
            mempty
    toBuiltinMeaning BData =
        makeBuiltinMeaning
            B
            mempty
    toBuiltinMeaning UnConstrData =
        makeBuiltinMeaning
            (\case
                Constr i ds -> EvaluationSuccess (i, ds)
                _           -> EvaluationFailure)
            mempty
    toBuiltinMeaning UnMapData =
        makeBuiltinMeaning
            (\case
                Map es -> EvaluationSuccess es
                _      -> EvaluationFailure)
            mempty
    toBuiltinMeaning UnListData =
        makeBuiltinMeaning
            (\case
                List ds -> EvaluationSuccess ds
                _       -> EvaluationFailure)
            mempty
    toBuiltinMeaning UnIData =
        makeBuiltinMeaning
            (\case
                I i -> EvaluationSuccess i
                _   -> EvaluationFailure)
            mempty
    toBuiltinMeaning UnBData =
        makeBuiltinMeaning
            (\case
                B b -> EvaluationSuccess b
                _   -> EvaluationFailure)
            mempty
    toBuiltinMeaning EqualsData =
        makeBuiltinMeaning
            ((==) @Data)
            mempty
    toBuiltinMeaning ChooseData =
        makeBuiltinMeaning
            (\xConstr xMap xList xI xB -> \case
                Constr {} -> xConstr
                Map    {} -> xMap
                List   {} -> xList
                I      {} -> xI
                B      {} -> xB)
            mempty

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
              EqualsString         -> 28
              EncodeUtf8           -> 29
              DecodeUtf8           -> 30
              Trace                -> 24
              Nop1                 -> 25
              Nop2                 -> 26
              Nop3                 -> 27
              FstPair              -> 31
              SndPair              -> 32
              NullList             -> 33
              HeadList             -> 34
              TailList             -> 35
              ConstrData           -> 36
              MapData              -> 37
              ListData             -> 38
              IData                -> 39
              BData                -> 40
              UnConstrData         -> 41
              UnMapData            -> 42
              UnListData           -> 43
              UnIData              -> 44
              UnBData              -> 45
              EqualsData           -> 46
              ChooseData           -> 47

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
              go 28 = pure EqualsString
              go 29 = pure EncodeUtf8
              go 30 = pure DecodeUtf8
              go 24 = pure Trace
              go 25 = pure Nop1
              go 26 = pure Nop2
              go 27 = pure Nop3
              go 31 = pure FstPair
              go 32 = pure SndPair
              go 33 = pure NullList
              go 34 = pure HeadList
              go 35 = pure TailList
              go 36 = pure ConstrData
              go 37 = pure MapData
              go 38 = pure ListData
              go 39 = pure IData
              go 40 = pure BData
              go 41 = pure UnConstrData
              go 42 = pure UnMapData
              go 43 = pure UnListData
              go 44 = pure UnIData
              go 45 = pure UnBData
              go 46 = pure EqualsData
              go 47 = pure ChooseData
              go _  = fail "Failed to decode BuiltinName"

-- It's set deliberately to give us "extra room" in the binary format to add things without running
-- out of space for tags (expanding the space would change the binary format for people who're
-- implementing it manually). So we have to set it manually.
-- | Using 7 bits to encode builtin tags.
builtinTagWidth :: NumBits
builtinTagWidth = 7

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
              EqualsString         -> 28
              EncodeUtf8           -> 29
              DecodeUtf8           -> 30
              Trace                -> 24
              Nop1                 -> 25
              Nop2                 -> 26
              Nop3                 -> 27
              FstPair              -> 31
              SndPair              -> 32
              NullList             -> 33
              HeadList             -> 34
              TailList             -> 35
              ConstrData           -> 36
              MapData              -> 37
              ListData             -> 38
              IData                -> 39
              BData                -> 40
              UnConstrData         -> 41
              UnMapData            -> 42
              UnListData           -> 43
              UnIData              -> 44
              UnBData              -> 45
              EqualsData           -> 46
              ChooseData           -> 47

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
              go 28 = pure EqualsString
              go 29 = pure EncodeUtf8
              go 30 = pure DecodeUtf8
              go 24 = pure Trace
              go 25 = pure Nop1
              go 26 = pure Nop2
              go 27 = pure Nop3
              go 31 = pure FstPair
              go 32 = pure SndPair
              go 33 = pure NullList
              go 34 = pure HeadList
              go 35 = pure TailList
              go 36 = pure ConstrData
              go 37 = pure MapData
              go 38 = pure ListData
              go 39 = pure IData
              go 40 = pure BData
              go 41 = pure UnConstrData
              go 42 = pure UnMapData
              go 43 = pure UnListData
              go 44 = pure UnIData
              go 45 = pure UnBData
              go 46 = pure EqualsData
              go 47 = pure ChooseData
              go _  = fail "Failed to decode BuiltinName"

    size _ n = n + builtinTagWidth

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

import           Control.DeepSeq
import           Crypto
import qualified Data.ByteString                                as BS
import qualified Data.ByteString.Hash                           as Hash
import           Data.Char
import           Data.Ix
import           Data.Text                                      (Text)
import           Data.Text.Encoding                             (decodeUtf8', encodeUtf8)
import           Data.Word                                      (Word8)
import           Flat                                           hiding (from, to)
import           Flat.Decoder
import           Flat.Encoder                                   as Flat

-- See Note [Pattern matching on built-in types].
-- TODO: should we have the commonest builtins at the front to have more compact encoding?
-- | Default built-in functions.
data DefaultFun
    -- Integers
    = AddInteger
    | SubtractInteger
    | MultiplyInteger
    | DivideInteger
    | QuotientInteger
    | RemainderInteger
    | ModInteger
    | EqualsInteger
    | LessThanInteger
    | LessThanEqualsInteger
    -- Bytestrings
    | AppendByteString
    | ConsByteString
    | SliceByteString
    | LengthOfByteString
    | IndexByteString
    | EqualsByteString
    | LessThanByteString
    | LessThanEqualsByteString
    -- Cryptography and hashes
    | Sha2_256
    | Sha3_256
    | Blake2b_256
    | VerifySignature
    -- Strings
    | AppendString
    | EqualsString
    | EncodeUtf8
    | DecodeUtf8
    -- Bool
    | IfThenElse
    -- Unit
    | ChooseUnit
    -- Tracing
    | Trace
    -- Pairs
    | FstPair
    | SndPair
    -- Lists
    | ChooseList
    | MkCons
    | HeadList
    | TailList
    | NullList
    -- Data
    -- It is convenient to have a "choosing" function for a data type that has more than two
    -- constructors to get pattern matching over it and we may end up having multiple such data
    -- types, hence we include the name of the data type as a suffix.
    | ChooseData
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
    -- Misc csontructors
    -- Constructors that we need for constructing e.g. Data. Polymorphic builtin
    -- constructors are often problematic (See note [Representable built-in functions over polymorphic built-in types])
    | MkPairData
    | MkNilData
    | MkNilPairData
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Hashable, Ix, PrettyBy PrettyConfigPlc)

instance Pretty DefaultFun where
    pretty fun = pretty $ case show fun of
        ""    -> ""  -- It's really weird to have a function's name displayed as an empty string,
                     -- but if it's what the 'Show' instance does, the user has asked for it.
        c : s -> toLower c : s

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
    toBuiltinMeaning LessThanEqualsInteger =
        makeBuiltinMeaning
            ((<=) @Integer)
            (runCostingFunTwoArguments . paramLessThanEqualsInteger)
    toBuiltinMeaning EqualsInteger =
        makeBuiltinMeaning
            ((==) @Integer)
            (runCostingFunTwoArguments . paramEqualsInteger)
    toBuiltinMeaning AppendByteString =
        makeBuiltinMeaning
            BS.append
            (runCostingFunTwoArguments . paramAppendByteString)
    toBuiltinMeaning ConsByteString =
        makeBuiltinMeaning
            (\n xs -> BS.cons (fromIntegral @Integer n) xs)
            mempty -- TODO: budget. To be replace with: (runCostingFunOneArgument . paramConsByteString)
    toBuiltinMeaning SliceByteString =
        makeBuiltinMeaning
            (\from to xs -> BS.take (to - from + 1) (BS.drop from xs))
            mempty -- TODO: budget. To be replace with: (runCostingFunOneArgument . paramSliceByteString)
    toBuiltinMeaning LengthOfByteString =
        makeBuiltinMeaning
            BS.length
            mempty -- TODO: budget. To be replace with: (runCostingFunOneArgument . paramLengthOfByteString)
    toBuiltinMeaning IndexByteString =
        makeBuiltinMeaning
            (\xs n -> if n >= 0 && n < BS.length xs then EvaluationSuccess $ toInteger $ BS.index xs n else EvaluationFailure)
            -- TODO: fix the mess above with `indexMaybe` from `bytestring >= 0.11.0.0`.
            mempty -- TODO: budget. To be replace with: (runCostingFunOneArgument . paramIndexByteString)
    toBuiltinMeaning Sha2_256 =
        makeBuiltinMeaning
            Hash.sha2
            (runCostingFunOneArgument . paramSha2_256)
    toBuiltinMeaning Sha3_256 =
        makeBuiltinMeaning
            Hash.sha3
            (runCostingFunOneArgument . paramSha3_256)
    toBuiltinMeaning Blake2b_256 =
        makeBuiltinMeaning
            Hash.blake2b
            mempty -- TODO: budget. To be replace with: (runCostingFunOneArgument . paramBlake2b)
    toBuiltinMeaning VerifySignature =
        makeBuiltinMeaning
            (verifySignature @EvaluationResult)
            (runCostingFunThreeArguments . paramVerifySignature)
    toBuiltinMeaning EqualsByteString =
        makeBuiltinMeaning
            ((==) @BS.ByteString)
            (runCostingFunTwoArguments . paramEqualsByteString)
    toBuiltinMeaning LessThanByteString =
        makeBuiltinMeaning
            ((<) @BS.ByteString)
            (runCostingFunTwoArguments . paramLessThanByteString)
    toBuiltinMeaning LessThanEqualsByteString =
        makeBuiltinMeaning
            ((<=) @BS.ByteString)
            (runCostingFunTwoArguments . paramLessThanEqualsByteString)
    toBuiltinMeaning IfThenElse =
       makeBuiltinMeaning
            (\b x y -> if b then x else y)
            (runCostingFunThreeArguments . paramIfThenElse)
    toBuiltinMeaning AppendString =
        makeBuiltinMeaning
            ((<>) :: Text -> Text -> Text)
            mempty  -- TODO: budget.
    toBuiltinMeaning EqualsString =
        makeBuiltinMeaning
            ((==) @Text)
            mempty  -- TODO: budget.
    toBuiltinMeaning EncodeUtf8 =
        makeBuiltinMeaning
            (encodeUtf8 :: Text -> BS.ByteString)
            mempty  -- TODO: budget.
    toBuiltinMeaning DecodeUtf8 =
        makeBuiltinMeaning
            (\bs -> case decodeUtf8' bs of { Right t -> EvaluationSuccess t ; Left _ -> EvaluationFailure })
            mempty  -- TODO: budget.
    toBuiltinMeaning Trace = makeBuiltinMeaning emitPlc mempty where
        emitPlc :: SomeConstantOf uni Text '[] -> Opaque term a -> Emitter (Opaque term a)
        emitPlc (SomeConstantOfRes _ s) t = emit s >> pure t
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
    toBuiltinMeaning ChooseList = makeBuiltinMeaning choosePlc mempty where
        choosePlc :: SomeConstantOf uni [] '[a] -> Opaque term b -> Opaque term b -> Opaque term b
        choosePlc (SomeConstantOfArg _ (SomeConstantOfRes _ xs)) a b = case xs of
            []    -> a
            _ : _ -> b
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
            (\d xConstr xMap xList xI xB -> case d of
                Constr {} -> xConstr
                Map    {} -> xMap
                List   {} -> xList
                I      {} -> xI
                B      {} -> xB)
            mempty
    toBuiltinMeaning ChooseUnit =
        makeBuiltinMeaning
            (\() a -> a)
            mempty
    toBuiltinMeaning MkPairData =
        makeBuiltinMeaning
            ((,) :: Data -> Data -> (Data, Data))
            mempty
    toBuiltinMeaning MkNilData =
        -- Nullary builtins don't work, so we need a unit argument
        makeBuiltinMeaning
            @(() -> [Data])
            (\() -> [])
            mempty
    toBuiltinMeaning MkNilPairData =
        -- Nullary builtins don't work, so we need a unit argument
        makeBuiltinMeaning
            @(() -> [(Data,Data)])
            (\() -> [])
            mempty
    toBuiltinMeaning MkCons = makeBuiltinMeaning consPlc mempty where
        consPlc
            :: SomeConstant uni a
            -> SomeConstantOf uni [] '[a]
            -> EvaluationResult (SomeConstantOf uni [] '[a])
        consPlc
            (SomeConstant (Some (ValueOf uniA x)))
            (SomeConstantOfArg uniA' (SomeConstantOfRes uniListA xs)) =
                -- Checking that the type of the constant is the same as the type of the elements
                -- of the unlifted list. Note that there's no way we could enforce this statically
                -- since in UPLC one can create an ill-typed program that attempts to prepend
                -- a value of the wrong type to a list.
                case uniA `geq` uniA' of
                    -- Should this rather be an 'UnliftingError'? For that we need
                    -- https://github.com/input-output-hk/plutus/pull/3035
                    Nothing   -> EvaluationFailure
                    Just Refl ->
                        EvaluationSuccess . SomeConstantOfArg uniA $
                            SomeConstantOfRes uniListA $ x : xs

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
              AddInteger               -> 0
              SubtractInteger          -> 1
              MultiplyInteger          -> 2
              DivideInteger            -> 3
              QuotientInteger          -> 4
              RemainderInteger         -> 5
              ModInteger               -> 6
              EqualsInteger            -> 7
              LessThanInteger          -> 8
              LessThanEqualsInteger    -> 9

              AppendByteString         -> 10
              ConsByteString           -> 11
              SliceByteString          -> 12
              LengthOfByteString       -> 13
              IndexByteString          -> 14
              EqualsByteString         -> 15
              LessThanByteString       -> 16
              LessThanEqualsByteString -> 17

              Sha2_256                 -> 18
              Sha3_256                 -> 19
              Blake2b_256              -> 20
              VerifySignature          -> 21

              AppendString             -> 22
              EqualsString             -> 23
              EncodeUtf8               -> 24
              DecodeUtf8               -> 25

              IfThenElse               -> 26

              ChooseUnit               -> 27

              Trace                    -> 28

              FstPair                  -> 29
              SndPair                  -> 30

              ChooseList               -> 31
              MkCons                   -> 32
              HeadList                 -> 33
              TailList                 -> 34
              NullList                 -> 35

              ChooseData               -> 36
              ConstrData               -> 37
              MapData                  -> 38
              ListData                 -> 39
              IData                    -> 40
              BData                    -> 41
              UnConstrData             -> 42
              UnMapData                -> 43
              UnListData               -> 44
              UnIData                  -> 45
              UnBData                  -> 46
              EqualsData               -> 47

              MkPairData               -> 48
              MkNilData                -> 49
              MkNilPairData            -> 50

    decode = go =<< decodeBuiltin
        where go 0  = pure AddInteger
              go 1  = pure SubtractInteger
              go 2  = pure MultiplyInteger
              go 3  = pure DivideInteger
              go 4  = pure QuotientInteger
              go 5  = pure RemainderInteger
              go 6  = pure ModInteger
              go 7  = pure EqualsInteger
              go 8  = pure LessThanInteger
              go 9  = pure LessThanEqualsInteger
              go 10 = pure AppendByteString
              go 11 = pure ConsByteString
              go 12 = pure SliceByteString
              go 13 = pure LengthOfByteString
              go 14 = pure IndexByteString
              go 15 = pure EqualsByteString
              go 16 = pure LessThanByteString
              go 17 = pure LessThanEqualsByteString
              go 18 = pure Sha2_256
              go 19 = pure Sha3_256
              go 20 = pure Blake2b_256
              go 21 = pure VerifySignature
              go 22 = pure AppendString
              go 23 = pure EqualsString
              go 24 = pure EncodeUtf8
              go 25 = pure DecodeUtf8
              go 26 = pure IfThenElse
              go 27 = pure ChooseUnit
              go 28 = pure Trace
              go 29 = pure FstPair
              go 30 = pure SndPair
              go 31 = pure ChooseList
              go 32 = pure MkCons
              go 33 = pure HeadList
              go 34 = pure TailList
              go 35 = pure NullList
              go 36 = pure ChooseData
              go 37 = pure ConstrData
              go 38 = pure MapData
              go 39 = pure ListData
              go 40 = pure IData
              go 41 = pure BData
              go 42 = pure UnConstrData
              go 43 = pure UnMapData
              go 44 = pure UnListData
              go 45 = pure UnIData
              go 46 = pure UnBData
              go 47 = pure EqualsData
              go 48 = pure MkPairData
              go 49 = pure MkNilData
              go 50 = pure MkNilPairData
              go t  = fail $ "Failed to decode builtin tag, got: " ++ show t

    size _ n = n + builtinTagWidth

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeApplications    #-}

module PlutusCore.Generators.Internal.Builtin (
    genConstant,
    genInteger,
    genByteString,
    genText,
    genData,
    genI,
    genB,
    genList,
    genMap,
    genConstr,
) where

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Data (Data (..))

import Data.ByteString qualified as BS
import Data.Int (Int64)
import Data.Kind qualified as GHC
import Data.Text (Text)
import Data.Type.Equality
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Type.Reflection
import Unsafe.Coerce

genConstant :: forall k (a :: k). TypeRep a -> Gen (Some (ValueOf DefaultUni))
genConstant tr
    | Just HRefl <- eqTypeRep tr (typeRep @()) = pure $ someValue ()
    | Just HRefl <- eqTypeRep tr (typeRep @Integer) = someValue <$> genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Int) = someValue <$> genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Bool) = someValue <$> Gen.bool
    | Just HRefl <- eqTypeRep tr (typeRep @BS.ByteString) = someValue <$> genByteString
    | Just HRefl <- eqTypeRep tr (typeRep @Text) = someValue <$> genText
    | Just HRefl <- eqTypeRep tr (typeRep @Data) = someValue <$> genData 5
    | trPair `App` tr1 `App` tr2 <- tr
    , Just HRefl <- eqTypeRep trPair (typeRep @(,)) = do
        Some (ValueOf uni1 val1) <- genConstant tr1
        Some (ValueOf uni2 val2) <- genConstant tr2
        pure $
            someValueOf
                (DefaultUniApply (DefaultUniApply DefaultUniProtoPair uni1) uni2)
                (val1, val2)
    | trList `App` trElem <- tr
    , Just HRefl <- eqTypeRep trList (typeRep @[]) = do
        Some (ValueOf uniElem (_ :: b)) <- genConstant trElem
        args <- Gen.list (Range.linear 0 10) $ genConstant trElem
        let valElems :: [b]
            valElems = (\(Some (ValueOf _ valElem')) -> unsafeCoerce valElem') <$> args
        pure $ someValueOf (DefaultUniApply DefaultUniProtoList uniElem) valElems
    | trOpaque `App` _ `App` trRep <- tr
    , Just HRefl <- eqTypeRep trOpaque (typeRep @Opaque) =
        genConstant trRep
    | trSomeConstant `App` _ `App` trRep <- tr
    , Just HRefl <- eqTypeRep trSomeConstant (typeRep @SomeConstant) =
        genConstant trRep
    | trTyVarRep `App` _ <- tr
    , Just HRefl <- eqTypeRep trTyVarRep (typeRep @(TyVarRep @GHC.Type)) =
        -- In the current implementation, all type variables are instantiated
        -- to `Integer` (TODO: change this).
        someValue <$> genInteger
    | otherwise =
        error $
            "genConstant: I don't know how to generate builtin arguments of this type: " <> show tr

----------------------------------------------------------
-- Generators

genInteger :: Gen Integer
genInteger = fromIntegral @Int64 <$> Gen.enumBounded

genByteString :: Gen BS.ByteString
genByteString = Gen.utf8 (Range.linear 0 100) Gen.enumBounded

genText :: Gen Text
genText = Gen.text (Range.linear 0 100) Gen.enumBounded

genData :: Int -> Gen Data
genData depth =
    Gen.choice $
        [genI, genB]
            <> [ genRec | depth > 1, genRec <-
                                        [ genList (depth - 1)
                                        , genMap (depth - 1)
                                        , genConstr (depth - 1)
                                        ]
               ]

genI :: Gen Data
genI = I <$> genInteger

genB :: Gen Data
genB = B <$> genByteString

genList :: Int -> Gen Data
genList depth = List <$> Gen.list (Range.linear 0 5) (genData (depth - 1))

genMap :: Int -> Gen Data
genMap depth =
    Map
        <$> Gen.list
            (Range.linear 0 5)
            ((,) <$> genData (depth - 1) <*> genData (depth - 1))

genConstr :: Int -> Gen Data
genConstr depth =
    Constr <$> genInteger
        <*> Gen.list
            (Range.linear 0 5)
            (genData (depth - 1))

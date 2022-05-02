{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module PlutusCore.Generators.Internal.Builtin (
    genTypeable,
    genConstant,
    genInteger,
    genByteString,
    genText,
    genData,
    genDataI,
    genDataB,
    genDataList,
    genDataMap,
    genDataConstr,
    matchTyCon,
) where

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Data (Data (..))
import PlutusCore.Generators.AST qualified as AST

import Data.ByteString qualified as BS
import Data.Int (Int64)
import Data.Text (Text)
import Data.Type.Equality
import Data.Typeable (splitTyConApp)
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Type.Reflection

genTypeable :: forall a. TypeRep a -> Gen a
genTypeable tr
    | Just HRefl <- eqTypeRep tr (typeRep @()) = pure ()
    | Just HRefl <- eqTypeRep tr (typeRep @Integer) = genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Int) = fromIntegral <$> genInteger
    | Just HRefl <- eqTypeRep tr (typeRep @Bool) = Gen.bool
    | Just HRefl <- eqTypeRep tr (typeRep @BS.ByteString) = genByteString
    | Just HRefl <- eqTypeRep tr (typeRep @Text) = genText
    | Just HRefl <- eqTypeRep tr (typeRep @Data) = genData
    | Just HRefl <- eqTypeRep tr (typeRep @(Term TyName Name DefaultUni DefaultFun ())) =
        AST.runAstGen AST.genTerm
    | trPair `App` tr1 `App` tr2 <- tr
    , Just HRefl <- eqTypeRep trPair (typeRep @(,)) =
        (,) <$> genTypeable tr1 <*> genTypeable tr2
    | trList `App` trElem <- tr
    , Just HRefl <- eqTypeRep trList (typeRep @[]) =
        Gen.list (Range.linear 0 10) $ genTypeable trElem
    | trOpaque `App` trVal `App` _ <- tr
    , Just HRefl <- eqTypeRep trOpaque (typeRep @Opaque) =
        Opaque <$> genTypeable trVal
    | trSomeConstant `App` trUni `App` _ <- tr
    , Just HRefl <- eqTypeRep trUni (typeRep @DefaultUni)
    , Just HRefl <- eqTypeRep trSomeConstant (typeRep @SomeConstant) =
        SomeConstant <$> genConstant
    | otherwise =
        error $
            "genTypeable: I don't know how to generate values of this type: " <> show tr

genConstant :: Gen (Some (ValueOf DefaultUni))
genConstant = AST.simpleRecursive nonRecursive recursive
  where
    nonRecursive =
        [ pure $ someValue ()
        , someValue <$> genInteger
        , someValue <$> Gen.bool
        , someValue <$> genByteString
        , someValue <$> genText
        ]
    recursive = [pairGen, listGen]
    pairGen = do
        Some (ValueOf uni1 val1) <- genConstant
        Some (ValueOf uni2 val2) <- genConstant
        pure $
            someValueOf
                (DefaultUniApply (DefaultUniApply DefaultUniProtoPair uni1) uni2)
                (val1, val2)
    listGen =
        let genList ::
                DefaultUni `Contains` a =>
                Gen a ->
                Gen (Some (ValueOf DefaultUni))
            genList = fmap someValue . Gen.list (Range.linear 0 10)
         in Gen.choice
                [ genList genInteger
                , genList Gen.bool
                , genList genByteString
                , genList genText
                , genList genData
                ]

-- | If the given `TypeRep`'s `TyCon` is @con@, return its type arguments.
matchTyCon :: forall con a. (Typeable con) => TypeRep a -> Maybe [SomeTypeRep]
matchTyCon tr = if con == con' then Just args else Nothing
  where
    (con, args) = splitTyConApp (SomeTypeRep tr)
    con' = typeRepTyCon (typeRep @con)

----------------------------------------------------------
-- Generators

genInteger :: Gen Integer
genInteger = fromIntegral @Int64 <$> Gen.enumBounded

genByteString :: Gen BS.ByteString
genByteString = Gen.utf8 (Range.linear 0 100) Gen.enumBounded

genText :: Gen Text
genText = Gen.text (Range.linear 0 100) Gen.enumBounded

genData :: Gen Data
genData = AST.simpleRecursive nonRecursive recursive
    where
        nonRecursive = [genDataI, genDataB]
        recursive = [genDataList, genDataMap, genDataConstr]

genDataI :: Gen Data
genDataI = I <$> genInteger

genDataB :: Gen Data
genDataB = B <$> genByteString

genDataList :: Gen Data
genDataList = List <$> Gen.list (Range.linear 0 5) genData

genDataMap :: Gen Data
genDataMap = Map <$> Gen.list (Range.linear 0 5) ((,) <$> genData <*> genData)

genDataConstr :: Gen Data
genDataConstr = Constr <$> genInteger <*> Gen.list (Range.linear 0 5) genData

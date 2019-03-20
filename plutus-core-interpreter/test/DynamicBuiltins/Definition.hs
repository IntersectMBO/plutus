-- | A dynamic built-in name test.

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module DynamicBuiltins.Definition
    ( test_definition
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Generators.Interesting

import qualified Language.PlutusCore.StdLib.Data.List       as Plc

import           Language.PlutusCore.Interpreter.CekMachine

import           DynamicBuiltins.Common

import           Data.Maybe
import           Data.Proxy
import           Hedgehog                                   hiding (Size, Var)
import qualified Hedgehog.Gen                               as Gen
import qualified Hedgehog.Range                             as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

dynamicFactorialName :: DynamicBuiltinName
dynamicFactorialName = DynamicBuiltinName "factorial"

dynamicFactorialMeaning :: DynamicBuiltinNameMeaning
dynamicFactorialMeaning = DynamicBuiltinNameMeaning sch fac where
    sch =
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)
    fac n = product [1..n]

dynamicFactorialDefinition :: DynamicBuiltinNameDefinition
dynamicFactorialDefinition =
    DynamicBuiltinNameDefinition dynamicFactorialName dynamicFactorialMeaning

dynamicFactorial :: Term tyname name ()
dynamicFactorial = dynamicBuiltinNameAsTerm dynamicFactorialName

-- | Check that the dynamic factorial defined above computes to the same thing as
-- a factorial defined in PLC itself.
test_dynamicFactorial :: TestTree
test_dynamicFactorial =
    testCase "dynamicFactorial" $ do
        let env = insertDynamicBuiltinNameDefinition dynamicFactorialDefinition mempty
            lhs = typecheckEvaluateCek env $ applyFactorial dynamicFactorial 3 10
            rhs = Right . evaluateCek mempty $ applyFactorial factorial 3 10
        lhs @?= rhs

dynamicReverseName :: DynamicBuiltinName
dynamicReverseName = DynamicBuiltinName "reverse"

dynamicReverseMeaning :: DynamicBuiltinNameMeaning
dynamicReverseMeaning = DynamicBuiltinNameMeaning sch (PlcList . Prelude.reverse . unPlcList) where
    sch =
        TypeSchemeAllType @"a" @0 Proxy $ \(_ :: TypedBuiltin size a) ->
            TypeSchemeBuiltin (TypedBuiltinDyn @(PlcList a)) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinDyn @(PlcList a))

dynamicReverseDefinition :: DynamicBuiltinNameDefinition
dynamicReverseDefinition =
    DynamicBuiltinNameDefinition dynamicReverseName dynamicReverseMeaning

dynamicReverse :: Term tyname name ()
dynamicReverse = dynamicBuiltinNameAsTerm dynamicReverseName

-- | Check that the dynamic reverse defined above computes to the same thing as
-- a reverse defined in PLC itself.
test_dynamicReverse :: TestTree
test_dynamicReverse =
    testProperty "dynamicReverse" . property $ do
        is <- forAll $ Gen.list (Range.linear 0 20) $ Gen.int (Range.linear 0 1000)
        let tIs = fromMaybe (error "Can't make a list") $ makeDynamicBuiltin (PlcList is)
            int8 = TyApp () (TyBuiltin () TyInteger) (TyInt () 8)
            runReverse rev = Apply () (TyInst () rev int8) tIs
            env = insertDynamicBuiltinNameDefinition dynamicReverseDefinition mempty
            getLhs = typecheckReadDynamicBuiltinCek env $ runReverse dynamicReverse
            rhs = readDynamicBuiltinCek mempty $ runReverse Plc.reverse
        getLhs === Right (Right . EvaluationSuccess . PlcList $ Prelude.reverse is)
        getLhs === Right rhs

test_definition :: TestTree
test_definition =
    testGroup "definition"
        [ test_dynamicFactorial
        , test_dynamicReverse
        ]

-- | A dynamic built-in name test.

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Evaluation.DynamicBuiltins.Definition
    ( test_definition
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.MkPlc

import           Language.PlutusCore.StdLib.Data.Bool
import qualified Language.PlutusCore.StdLib.Data.Function           as Plc

import           Evaluation.DynamicBuiltins.Common

import           Data.Either                                        (isRight)
import           Data.Proxy
import           Hedgehog                                           hiding (Size, Var)
import qualified Hedgehog.Gen                                       as Gen
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

dynamicFactorialName :: DynamicBuiltinName
dynamicFactorialName = DynamicBuiltinName "factorial"

dynamicFactorialMeaning
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => DynamicBuiltinNameMeaning uni
dynamicFactorialMeaning = DynamicBuiltinNameMeaning sch fac (\_ -> ExBudget 1 1) where
    sch = Proxy @Integer `TypeSchemeArrow` TypeSchemeResult Proxy
    fac n = product [1..n]

dynamicFactorialDefinition
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => DynamicBuiltinNameDefinition uni
dynamicFactorialDefinition =
    DynamicBuiltinNameDefinition dynamicFactorialName dynamicFactorialMeaning

dynamicFactorial :: Term tyname name uni ()
dynamicFactorial = dynamicBuiltinNameAsTerm dynamicFactorialName

-- | Check that the dynamic factorial defined above computes to the same thing as
-- a factorial defined in PLC itself.
test_dynamicFactorial :: TestTree
test_dynamicFactorial =
    testCase "dynamicFactorial" $ do
        let env = insertDynamicBuiltinNameDefinition dynamicFactorialDefinition mempty
            ten = mkConstant @Integer @DefaultUni () 10
            lhs = typecheckEvaluateCek env $ Apply () dynamicFactorial ten
            rhs = typecheckEvaluateCek mempty $ Apply () factorial ten
        assertBool "type checks" $ isRight lhs
        lhs @?= rhs

dynamicConstName :: DynamicBuiltinName
dynamicConstName = DynamicBuiltinName "const"

dynamicConstMeaning :: DynamicBuiltinNameMeaning uni
dynamicConstMeaning = DynamicBuiltinNameMeaning sch Prelude.const (\_ _ -> ExBudget 1 1) where
    sch =
        TypeSchemeAllType @"a" @0 Proxy $ \a ->
        TypeSchemeAllType @"b" @1 Proxy $ \b ->
            a `TypeSchemeArrow` b `TypeSchemeArrow` TypeSchemeResult a

dynamicConstDefinition :: DynamicBuiltinNameDefinition uni
dynamicConstDefinition =
    DynamicBuiltinNameDefinition dynamicConstName dynamicConstMeaning

dynamicConst :: Term tyname name uni ()
dynamicConst = dynamicBuiltinNameAsTerm dynamicConstName

-- | Check that the dynamic const defined above computes to the same thing as
-- a const defined in PLC itself.
test_dynamicConst :: TestTree
test_dynamicConst =
    testProperty "dynamicConst" . property $ do
        c <- forAll Gen.unicode
        b <- forAll Gen.bool
        let tC = makeKnown c
            tB = makeKnown b
            char = toTypeAst @DefaultUni @Char Proxy
            runConst con = mkIterApp () (mkIterInst () con [char, bool]) [tC, tB]
            env = insertDynamicBuiltinNameDefinition dynamicConstDefinition mempty
            lhs = typecheckReadKnownCek env $ runConst dynamicConst
            rhs = typecheckReadKnownCek mempty $ runConst Plc.const
        lhs === Right (Right c)
        lhs === rhs

dynamicIdName :: DynamicBuiltinName
dynamicIdName = DynamicBuiltinName "id"

dynamicIdMeaning :: DynamicBuiltinNameMeaning uni
dynamicIdMeaning = DynamicBuiltinNameMeaning sch Prelude.id (\_ -> ExBudget 1 1) where
    sch =
        TypeSchemeAllType @"a" @0 Proxy $ \a ->
            a `TypeSchemeArrow` TypeSchemeResult a

dynamicIdDefinition :: DynamicBuiltinNameDefinition uni
dynamicIdDefinition =
    DynamicBuiltinNameDefinition dynamicIdName dynamicIdMeaning

dynamicId :: Term tyname name uni ()
dynamicId = dynamicBuiltinNameAsTerm dynamicIdName

-- | Test that a polymorphic built-in function doesn't subvert the CEK machine.
-- See https://github.com/input-output-hk/plutus/issues/1882
test_dynamicId :: TestTree
test_dynamicId =
    testCase "dynamicId" $ do
        let env = insertDynamicBuiltinNameDefinition dynamicIdDefinition mempty
            zer = mkConstant @Integer @DefaultUni () 0
            one = mkConstant @Integer @DefaultUni () 1
            integer = mkTyBuiltin @Integer ()
            -- id {integer -> integer} ((\(i : integer) (j : integer) -> i) 1) 0
            term =
                mkIterApp () (TyInst () dynamicId (TyFun () integer integer))
                    [ Apply () constIntegerInteger one
                    , zer
                    ] where
                          constIntegerInteger = runQuote $ do
                              i <- freshName () "i"
                              j <- freshName () "j"
                              return
                                  . LamAbs () i integer
                                  . LamAbs () j integer
                                  $ Var () i
        typecheckEvaluateCek env term @?= Right (EvaluationSuccess one)

test_definition :: TestTree
test_definition =
    testGroup "definition"
        [ test_dynamicFactorial
        , test_dynamicConst
        , test_dynamicId
        ]

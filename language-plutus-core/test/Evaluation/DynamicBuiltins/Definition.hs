-- | A dynamic built-in name test.

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators         #-}

module Evaluation.DynamicBuiltins.Definition
    ( test_definition
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.MkPlc

import           Language.PlutusCore.StdLib.Data.Bool
import qualified Language.PlutusCore.StdLib.Data.List               as Plc
import qualified Language.PlutusCore.StdLib.Data.Function           as Plc
import           Language.PlutusCore.Evaluation.Machine.Cek         (CekValue)

import           Evaluation.DynamicBuiltins.Common

import           Data.Either                                        (isRight)
import           Data.Proxy
import           Hedgehog                                           hiding (Opaque, Size, Var)
import qualified Hedgehog.Gen                                       as Gen
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

dynamicFactorialName :: DynamicBuiltinName
dynamicFactorialName = DynamicBuiltinName "factorial"

dynamicFactorialMeaning
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => DynamicBuiltinNameMeaning term
dynamicFactorialMeaning = DynamicBuiltinNameMeaning sch fac (\_ -> ExBudget 1 1) where
    sch = Proxy @Integer `TypeSchemeArrow` TypeSchemeResult Proxy
    fac n = product [1..n]

dynamicFactorialDefinition
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => DynamicBuiltinNameDefinition term
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

dynamicConstMeaning :: DynamicBuiltinNameMeaning term
dynamicConstMeaning = DynamicBuiltinNameMeaning sch Prelude.const (\_ _ -> ExBudget 1 1) where
    sch =
        TypeSchemeAll @"a" @0 Proxy (Type ()) $ \a ->
        TypeSchemeAll @"b" @1 Proxy (Type ()) $ \b ->
            a `TypeSchemeArrow` b `TypeSchemeArrow` TypeSchemeResult a

dynamicConstDefinition :: DynamicBuiltinNameDefinition term
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
        let tC = mkConstant () c
            tB = mkConstant () b
            char = toTypeAst @DefaultUni @Char Proxy
            runConst con = mkIterApp () (mkIterInst () con [char, bool]) [tC, tB]
            env = insertDynamicBuiltinNameDefinition dynamicConstDefinition mempty
            lhs = typecheckReadKnownCek env $ runConst dynamicConst
            rhs = typecheckReadKnownCek mempty $ runConst Plc.const
        lhs === Right (Right c)
        lhs === rhs

dynamicIdName :: DynamicBuiltinName
dynamicIdName = DynamicBuiltinName "id"

dynamicIdMeaning :: DynamicBuiltinNameMeaning term
dynamicIdMeaning = DynamicBuiltinNameMeaning sch Prelude.id (\_ -> ExBudget 1 1) where
    sch =
        TypeSchemeAll @"a" @0 Proxy (Type ()) $ \a ->
            a `TypeSchemeArrow` TypeSchemeResult a

dynamicIdDefinition :: DynamicBuiltinNameDefinition term
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
                              i <- freshName "i"
                              j <- freshName "j"
                              return
                                  . LamAbs () i integer
                                  . LamAbs () j integer
                                  $ Var () i
        typecheckEvaluateCek env term @?= Right (EvaluationSuccess one)

dynamicIdFIntegerName :: DynamicBuiltinName
dynamicIdFIntegerName = DynamicBuiltinName "idFInteger"

-- >>> :set -XTypeApplications
-- >>> import Language.PlutusCore.Pretty
-- >>> putStrLn . render . prettyPlcReadableDef . dynamicBuiltinNameMeaningToType $ dynamicIdFIntegerMeaning @DefaultUni
-- (all (f :: * -> *). f integer -> f integer)
dynamicIdFIntegerMeaning
    :: uni `Includes` Integer => DynamicBuiltinNameMeaning (CekValue uni)
dynamicIdFIntegerMeaning = DynamicBuiltinNameMeaning sch Prelude.id (\_ -> ExBudget 1 1) where
    sch =
        TypeSchemeAll @"f" @0 Proxy (KindArrow () (Type ()) $ Type ()) $ \(_ :: Proxy f) ->
            let ty = Proxy @(Opaque _ (TyAppRep f Integer))
            in ty `TypeSchemeArrow` TypeSchemeResult ty

dynamicIdFIntegerDefinition
    :: uni `Includes` Integer => DynamicBuiltinNameDefinition (CekValue uni)
dynamicIdFIntegerDefinition =
    DynamicBuiltinNameDefinition dynamicIdFIntegerName dynamicIdFIntegerMeaning

dynamicIdFInteger :: Term tyname name uni ()
dynamicIdFInteger = dynamicBuiltinNameAsTerm dynamicIdFIntegerName

-- | Test that a polymorphic built-in function can have a higher-kinded type variable in its
-- signature.
test_dynamicIdFInteger :: TestTree
test_dynamicIdFInteger =
    testCase "dynamicIdFInteger" $ do
        let env = insertDynamicBuiltinNameDefinition dynamicIdFIntegerDefinition mempty
            one = mkConstant @Integer @DefaultUni () 1
            ten = mkConstant @Integer @DefaultUni () 10
            res = mkConstant @Integer @DefaultUni () 55
            -- sum (idFInteger {list} (enumFromTo 1 10))
            term
                = Apply () Plc.sum
                . Apply () (TyInst () dynamicIdFInteger Plc.listTy)
                $ mkIterApp () Plc.enumFromTo [one, ten]
        typecheckEvaluateCek env term @?= Right (EvaluationSuccess res)

data ListRep a
instance KnownTypeAst uni a => KnownTypeAst uni (ListRep a) where
    toTypeAst _ = TyApp () Plc.listTy . toTypeAst $ Proxy @a

dynamicIdListName :: DynamicBuiltinName
dynamicIdListName = DynamicBuiltinName "idList"

-- >>> :set -XTypeApplications
-- >>> import Language.PlutusCore.Pretty
-- >>> putStrLn . render . prettyPlcReadableDef . dynamicBuiltinNameMeaningToType $ dynamicIdListMeaning @DefaultUni
-- (all (a :: *). (\(a :: *) -> ifix (\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r) a) a -> (\(a :: *) -> ifix (\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r) a) a)
dynamicIdListMeaning :: DynamicBuiltinNameMeaning (CekValue uni)
dynamicIdListMeaning = DynamicBuiltinNameMeaning sch Prelude.id (\_ -> ExBudget 1 1) where
    sch =
        TypeSchemeAll @"a" @0 Proxy (Type ()) $ \(_ :: Proxy a) ->
            let ty = Proxy @(Opaque _ (ListRep a))
            in ty `TypeSchemeArrow` TypeSchemeResult ty

dynamicIdListDefinition :: DynamicBuiltinNameDefinition (CekValue uni)
dynamicIdListDefinition =
    DynamicBuiltinNameDefinition dynamicIdListName dynamicIdListMeaning

dynamicIdList :: Term tyname name uni ()
dynamicIdList = dynamicBuiltinNameAsTerm dynamicIdListName

-- | Test that opaque terms with custom types are allowed.
test_dynamicIdList :: TestTree
test_dynamicIdList =
    testCase "dynamicIdList" $ do
        let env = insertDynamicBuiltinNameDefinition dynamicIdListDefinition mempty
            one = mkConstant @Integer @DefaultUni () 1
            ten = mkConstant @Integer @DefaultUni () 10
            res = mkConstant @Integer @DefaultUni () 55
            integer = mkTyBuiltin @Integer ()
            -- sum (idList {integer} (enumFromTo 1 10))
            term
                = Apply () Plc.sum
                . Apply () (TyInst () dynamicIdList integer)
                $ mkIterApp () Plc.enumFromTo [one, ten]
        typecheckEvaluateCek env term @?= Right (EvaluationSuccess res)

test_definition :: TestTree
test_definition =
    testGroup "definition"
        [ test_dynamicFactorial
        , test_dynamicConst
        , test_dynamicId
        , test_dynamicIdFInteger
        , test_dynamicIdList
        ]

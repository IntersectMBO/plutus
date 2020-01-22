-- | A dynamic built-in name test.

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Evaluation.DynamicBuiltins.Definition
    ( test_definition
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.MkPlc

import qualified Language.PlutusCore.StdLib.Data.Bool       as Plc
import qualified Language.PlutusCore.StdLib.Data.Function   as Plc
import qualified Language.PlutusCore.StdLib.Data.List       as Plc
import           Language.PlutusCore.StdLib.Data.Unit

import           Evaluation.DynamicBuiltins.Common

import           Control.Monad.IO.Class
import           Data.Either                                (isRight)
import           Data.Proxy
import           Hedgehog                                   hiding (Size, Var, eval)
import qualified Hedgehog.Gen                               as Gen
import qualified Hedgehog.Range                             as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

dynamicFactorialName :: DynamicBuiltinName
dynamicFactorialName = DynamicBuiltinName "factorial"

dynamicFactorialMeaning :: DynamicBuiltinNameMeaning
dynamicFactorialMeaning = DynamicBuiltinNameMeaning sch fac where
    sch = Proxy @Integer `TypeSchemeArrow` TypeSchemeResult Proxy
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
            lhs = typecheckEvaluateCek env $ Apply () dynamicFactorial (makeIntConstant 10)
            rhs = typecheckEvaluateCek mempty $ Apply () factorial (makeIntConstant 10)
        assertBool "type checks" $ isRight lhs
        lhs @?= rhs

dynamicConstName :: DynamicBuiltinName
dynamicConstName = DynamicBuiltinName "const"

dynamicConstMeaning :: DynamicBuiltinNameMeaning
dynamicConstMeaning = DynamicBuiltinNameMeaning sch Prelude.const where
    sch =
        TypeSchemeAllType @"a" @0 Proxy $ \a ->
        TypeSchemeAllType @"b" @1 Proxy $ \b ->
            a `TypeSchemeArrow` b `TypeSchemeArrow` TypeSchemeResult a

dynamicConstDefinition :: DynamicBuiltinNameDefinition
dynamicConstDefinition =
    DynamicBuiltinNameDefinition dynamicConstName dynamicConstMeaning

dynamicConst :: Term tyname name ()
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
            char = toTypeAst @Char Proxy
            runConst con = mkIterApp () (mkIterInst () con [char, Plc.bool]) [tC, tB]
            env = insertDynamicBuiltinNameDefinition dynamicConstDefinition mempty
            lhs = typecheckReadKnownCek env $ runConst dynamicConst
            rhs = typecheckReadKnownCek mempty $ runConst Plc.const
        lhs === Right (Right (EvaluationSuccess c))
        lhs === rhs

dynamicReverseName :: DynamicBuiltinName
dynamicReverseName = DynamicBuiltinName "reverse"

dynamicReverseMeaning :: DynamicBuiltinNameMeaning
dynamicReverseMeaning = DynamicBuiltinNameMeaning sch (PlcList . Prelude.reverse . unPlcList) where
    sch =
        TypeSchemeAllType @"a" @0 Proxy $ \(_ :: Proxy a) ->
            Proxy @(PlcList a) `TypeSchemeArrow` TypeSchemeResult (Proxy @(PlcList a))

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
        is <- forAll . Gen.list (Range.linear 0 10) $ Gen.int (Range.linear 0 1000)
        let tIs = makeKnown $ PlcList is
            int = toTypeAst @Int Proxy
            runReverse rev = Apply () (TyInst () rev int) tIs
            env = insertDynamicBuiltinNameDefinition dynamicReverseDefinition mempty
            lhs = typecheckReadKnownCek env $ runReverse dynamicReverse
            rhs = typecheckReadKnownCek mempty $ runReverse Plc.reverse
        lhs === Right (Right (EvaluationSuccess . PlcList $ Prelude.reverse is))
        lhs === rhs

dynamicCatchErrorName :: DynamicBuiltinName
dynamicCatchErrorName = DynamicBuiltinName "catchError"

dynamicCatchErrorMeaning :: DynamicBuiltinNameMeaning
dynamicCatchErrorMeaning = DynamicBuiltinNameMeaning sch mean where
    sch =
        TypeSchemeAllType @"a" @0 Proxy $ \(a :: Proxy a) ->
            Proxy @(EvaluationResult a) `TypeSchemeArrow` a `TypeSchemeArrow` TypeSchemeResult a

    mean (EvaluationSuccess a) _ = a
    mean EvaluationFailure     b = b

dynamicCatchErrorDefinition :: DynamicBuiltinNameDefinition
dynamicCatchErrorDefinition =
    DynamicBuiltinNameDefinition dynamicCatchErrorName dynamicCatchErrorMeaning

dynamicCatchError :: Term tyname name ()
dynamicCatchError = dynamicBuiltinNameAsTerm dynamicCatchErrorName

-- | Check that it's possible to catch errors on the Plutus side using a builtin.
test_dynamicCatchError :: TestTree
test_dynamicCatchError =
    testProperty "dynamicCatchError" . property $ do
        i <- forAll . Gen.integral $ Range.linear 0 100
        j <- forAll . Gen.integral $ Range.linear 0 100
        let integer = toTypeAst @Integer Proxy
            env = insertDynamicBuiltinNameDefinition dynamicCatchErrorDefinition mempty
            lhs =
                typecheckReadKnownCek env $
                    -- catchError (divideInteger i j) i
                    mkIterApp () (TyInst () dynamicCatchError integer)
                        [ mkIterApp () (builtinNameAsTerm DivideInteger)
                            [ makeKnown i
                            , makeKnown j
                            ]
                        , makeKnown i
                        ]
            res = if j /= 0 then i `div` j else i :: Integer
        lhs === Right (Right (EvaluationSuccess res))

dynamicOnErrorName :: DynamicBuiltinName
dynamicOnErrorName = DynamicBuiltinName "onError"

dynamicOnErrorMeaning :: DynamicBuiltinNameMeaning
dynamicOnErrorMeaning = DynamicBuiltinNameMeaning sch mean where
    sch =
        TypeSchemeAllType @"a" @0 Proxy $ \(_ :: Proxy a) ->
            Proxy @(EvaluationResult a) `TypeSchemeArrow`
            Proxy @(RawTerm (() -> ())) `TypeSchemeArrow`
            TypeSchemeResult (Proxy @a)

    mean (EvaluationSuccess a) _           = a
    mean a@EvaluationFailure   (RawTerm f) =
        -- I made a mistake here, but the type checker didn't catch it.
        -- We do not type check meanings of builtins. Not sure if it's even possible.
        let x = toTypeAst $ proxyOf a in
            OpaqueTerm $ mkIterApp () (mkIterInst () Plc.const [x, unit])
                [ Error () x
                , Apply () f unitval
                ]

    proxyOf :: a -> Proxy a
    proxyOf _ = Proxy

dynamicOnErrorDefinition :: DynamicBuiltinNameDefinition
dynamicOnErrorDefinition =
    DynamicBuiltinNameDefinition dynamicOnErrorName dynamicOnErrorMeaning

dynamicOnError :: Term tyname name ()
dynamicOnError = dynamicBuiltinNameAsTerm dynamicOnErrorName

-- | Check that it's possible to do something on error on the Plutus side using a builtin.
test_dynamicOnError :: TestTree
test_dynamicOnError =
    testProperty "dynamicOnError" . property $ do
        i <- forAll . Gen.integral $ Range.linear 0 100
        j <- forAll . Gen.integral $ Range.linear 0 100
        let integer = toTypeAst @Integer Proxy
            env = insertDynamicBuiltinNameDefinition dynamicOnErrorDefinition mempty
        (is, lhs) <-
            liftIO . withEmitEvaluateBy typecheckEvaluateCek env $ \emit ->
                -- onError (divideInteger i j) (\(_ : ()) -> emit i)
                mkIterApp () (TyInst () dynamicOnError integer)
                    [ mkIterApp () (builtinNameAsTerm DivideInteger)
                        [ makeKnown i
                        , makeKnown j
                        ]
                    , runQuote $ do
                        -- It's safe to prepend a lambda here, because the body can't
                        -- contain any variables.
                        u <- freshName () "u"
                        pure
                            . LamAbs () u unit
                            . Apply () emit
                            $ makeKnown (i :: Integer)
                    ]
        if j == 0
            then do
                -- @i@ is emitted on failure.
                lhs === Right EvaluationFailure
                is === [i]
            else do
                -- @i@ is not emitted on success.
                lhs === Right (EvaluationSuccess . makeKnown $ i `div` j)
                is === []

test_definition :: TestTree
test_definition =
    testGroup "definition"
        [ test_dynamicFactorial
        , test_dynamicConst
        , test_dynamicReverse
        , test_dynamicCatchError
        , test_dynamicOnError
        ]

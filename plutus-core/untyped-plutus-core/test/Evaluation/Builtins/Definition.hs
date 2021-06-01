-- | Tests for all kinds of built-in functions.

{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}

-- Sure GHC, I'm enabling the extension just so that you can warn be about its usages.
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Evaluation.Builtins.Definition
    ( test_definition
    ) where

import           PlutusCore
import           PlutusCore.Constant
import           PlutusCore.Evaluation.Machine.MachineParameters
import           PlutusCore.Generators.Interesting
import           PlutusCore.MkPlc                                hiding (error)

import           PlutusCore.Examples.Builtins
import           PlutusCore.StdLib.Data.Bool
import qualified PlutusCore.StdLib.Data.Function                 as Plc
import qualified PlutusCore.StdLib.Data.List                     as Plc

import           Evaluation.Builtins.Common

import           UntypedPlutusCore.Evaluation.Machine.Cek

import           Control.Exception
import           Data.Either
import           Data.Proxy
import           Hedgehog                                        hiding (Opaque, Size, Var)
import qualified Hedgehog.Gen                                    as Gen
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog

defaultCekParametersExt
    :: MachineParameters CekMachineCosts CekValue DefaultUni (Either DefaultFun ExtensionFun)
defaultCekParametersExt =
    toMachineParameters $ CostModel defaultCekMachineCosts (defaultBuiltinCostModel, ())

-- | Check that 'Factorial' from the above computes to the same thing as
-- a factorial defined in PLC itself.
test_Factorial :: TestTree
test_Factorial =
    testCase "Factorial" $ do
        let ten = mkConstant @Integer @DefaultUni () 10
            lhs = typecheckEvaluateCek defaultCekParametersExt $
                    apply () (builtin () $ Right Factorial) ten
            rhs = typecheckEvaluateCek defaultCekParametersExt $
                    apply () (mapFun Left factorial) ten
        assertBool "type checks" $ isRight lhs
        lhs @?= rhs

-- | Check that 'Const' from the above computes to the same thing as
-- a const defined in PLC itself.
test_Const :: TestTree
test_Const =
    testProperty "Const" . property $ do
        c <- forAll Gen.unicode
        b <- forAll Gen.bool
        let tC = mkConstant () c
            tB = mkConstant () b
            char = toTypeAst @_ @DefaultUni @Char Proxy
            runConst con = mkIterApp () (mkIterInst () con [char, bool]) [tC, tB]
            lhs = typecheckReadKnownCek defaultCekParametersExt $ runConst $ builtin () (Right Const)
            rhs = typecheckReadKnownCek defaultCekParametersExt $ runConst $ mapFun Left Plc.const
        lhs === Right (Right c)
        lhs === rhs

-- | Test that a polymorphic built-in function doesn't subvert the CEK machine.
-- See https://github.com/input-output-hk/plutus/issues/1882
test_Id :: TestTree
test_Id =
    testCase "Id" $ do
        let zer = mkConstant @Integer @DefaultUni () 0
            oneT = mkConstant @Integer @DefaultUni () 1
            oneU = mkConstant @Integer @DefaultUni () 1
            integer = mkTyBuiltin @Integer ()
            -- id {integer -> integer} ((\(i : integer) (j : integer) -> i) 1) 0
            term =
                mkIterApp () (tyInst () (builtin () $ Right Id) (TyFun () integer integer))
                    [ apply () constIntegerInteger oneT
                    , zer
                    ] where
                          constIntegerInteger = runQuote $ do
                              i <- freshName "i"
                              j <- freshName "j"
                              return
                                  . LamAbs () i integer
                                  . LamAbs () j integer
                                  $ Var () i
        typecheckEvaluateCekNoEmit defaultCekParametersExt term @?= Right (EvaluationSuccess oneU)

-- | Test that a polymorphic built-in function can have a higher-kinded type variable in its
-- signature.
test_IdFInteger :: TestTree
test_IdFInteger =
    testCase "IdFInteger" $ do
        let one = mkConstant @Integer @DefaultUni () 1
            ten = mkConstant @Integer @DefaultUni () 10
            res = mkConstant @Integer @DefaultUni () 55
            -- sum (idFInteger {list} (enumFromTo 1 10))
            term
                = apply () (mapFun Left Plc.sum)
                . apply () (tyInst () (builtin () $ Right IdFInteger) Plc.listTy)
                $ mkIterApp () (mapFun Left Plc.enumFromTo) [one, ten]
        typecheckEvaluateCekNoEmit defaultCekParametersExt term @?= Right (EvaluationSuccess res)

test_IdList :: TestTree
test_IdList =
    testCase "IdList" $ do
        let tyAct = typeOfBuiltinFunction @DefaultUni IdList
            tyExp = let a = TyName . Name "a" $ Unique 0
                        listA = TyApp () Plc.listTy (TyVar () a)
                    in TyForall () a (Type ()) $ TyFun () listA listA
            one = mkConstant @Integer @DefaultUni () 1
            ten = mkConstant @Integer @DefaultUni () 10
            res = mkConstant @Integer @DefaultUni () 55
            integer = mkTyBuiltin @Integer ()
            -- sum (idList {integer} (enumFromTo 1 10))
            term
                = apply () (mapFun Left Plc.sum)
                . apply () (tyInst () (builtin () $ Right IdList) integer)
                $ mkIterApp () (mapFun Left Plc.enumFromTo) [one, ten]
        tyAct @?= tyExp
        typecheckEvaluateCekNoEmit defaultCekParametersExt term @?= Right (EvaluationSuccess res)

{- Note [Higher-rank built-in functions]
We can't unlift a monomorphic function passed to a built-in function, let alone unlift a polymorphic
one, however we can define a built-in function that accepts an 'Opaque' term of a polymorphic type.
However, as is always the case with an 'Opaque' term, we can't inspect it or use it in any
non-opaque way, so a function of type

    all (f :: * -> *). (all (a :: *). f a) -> all (a :: *). f a

can be assigned the following meaning on the Haskell side:

    \x -> x

but we have no way of providing a meaning for a built-in function with the following signature:

    all (f :: * -> *). all (a :: *). (all (a :: *). f a) -> f a

That's because the meaning function would have to instantiate the @all (a :: *). f a@ argument
somehow to get an @f a@, but that is exactly "using a term in a non-opaque way".

Basically, since we are either generic over @term@ or, like in the example below, use 'CekValue',
there's is no sensible way of instantiating a passed polymorphic argument (or applying a passed
argument when it's a function, for another example).
-}

-- | Test that opaque terms with higher-rank types are allowed.
test_IdRank2 :: TestTree
test_IdRank2 =
    testCase "IdRank2" $ do
        let res = mkConstant @Integer @DefaultUni () 0
            integer = mkTyBuiltin @Integer ()
            -- sum (idRank2 {list} nil {integer})
            term
                = apply () (mapFun Left Plc.sum)
                . tyInst () (apply () (tyInst () (builtin () $ Right IdRank2) Plc.listTy) Plc.nil)
                $ integer
        typecheckEvaluateCekNoEmit defaultCekParametersExt term @?= Right (EvaluationSuccess res)

-- | Test that an exception thrown in the builtin application code does not get caught in the CEK
-- machine and blows in the caller face instead.
test_FailingPlus :: TestTree
test_FailingPlus =
    testCase "FailingPlus" $ do
        let term =
                mkIterApp () (builtin () $ Right FailingPlus)
                    [ mkConstant @Integer @DefaultUni () 0
                    , mkConstant @Integer @DefaultUni () 1
                    ]
        typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
            -- Here we rely on 'typecheckAnd' lazily running the action after type checking the term.
            traverse (try . evaluate) $ typecheckEvaluateCekNoEmit defaultCekParametersExt term
        typeErrOrEvalExcOrRes @?= Right (Left BuiltinErrorCall)

-- | Test that evaluating a PLC builtin application that is expensive enough to exceed the budget
-- does not result in actual evaluation of the application on the Haskell side and instead we get an
-- 'EvaluationFailure'.
test_ExpensivePlus :: TestTree
test_ExpensivePlus =
    testCase "ExpensivePlus" $ do
        let term =
                mkIterApp () (builtin () $ Right ExpensivePlus)
                    [ mkConstant @Integer @DefaultUni () 0
                    , mkConstant @Integer @DefaultUni () 1
                    ]
        typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
            traverse (try . evaluate) $ typecheckEvaluateCekNoEmit defaultCekParametersExt term
        typeErrOrEvalExcOrRes @?= Right (Right EvaluationFailure)

test_definition :: TestTree
test_definition =
    testGroup "definition"
        [ test_Factorial
        , test_Const
        , test_Id
        , test_IdFInteger
        , test_IdList
        , test_IdRank2
        , test_FailingPlus
        , test_ExpensivePlus
        ]

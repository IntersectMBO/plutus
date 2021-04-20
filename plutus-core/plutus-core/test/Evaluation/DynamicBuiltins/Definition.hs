-- | A dynamic built-in name test.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.DynamicBuiltins.Definition
    ( test_definition
    ) where

import           PlutusCore
import           PlutusCore.Constant
import           PlutusCore.Generators.Interesting
import           PlutusCore.MkPlc                  hiding (error)

import           PlutusCore.Examples.Builtins
import           PlutusCore.StdLib.Data.Bool
import qualified PlutusCore.StdLib.Data.Function   as Plc
import qualified PlutusCore.StdLib.Data.List       as Plc

import           Evaluation.DynamicBuiltins.Common

import           Data.Either
import           Data.Proxy
import           Hedgehog                          hiding (Opaque, Size, Var)
import qualified Hedgehog.Gen                      as Gen
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog

-- | Check that 'Factorial' from the above computes to the same thing as
-- a factorial defined in PLC itself.
test_Factorial :: TestTree
test_Factorial =
    testCase "Factorial" $ do
        let ten = mkConstant @Integer @DefaultUni () 10
            lhs = typecheckEvaluateCk defBuiltinsRuntimeExt $ Apply () (Builtin () $ Right Factorial) ten
            rhs = typecheckEvaluateCk defBuiltinsRuntimeExt $ Apply () (mapFun Left factorial) ten
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
            lhs = typecheckReadKnownCk defBuiltinsRuntimeExt $ runConst $ Builtin () (Right Const)
            rhs = typecheckReadKnownCk defBuiltinsRuntimeExt $ runConst $ mapFun Left Plc.const
        lhs === Right (Right c)
        lhs === rhs

-- | Test that a polymorphic built-in function doesn't subvert the CEK machine.
-- See https://github.com/input-output-hk/plutus/issues/1882
test_Id :: TestTree
test_Id =
    testCase "Id" $ do
        let zer = mkConstant @Integer @DefaultUni () 0
            one = mkConstant @Integer @DefaultUni () 1
            integer = mkTyBuiltin @Integer ()
            -- id {integer -> integer} ((\(i : integer) (j : integer) -> i) 1) 0
            term =
                mkIterApp () (TyInst () (Builtin () $ Right Id) (TyFun () integer integer))
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
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess one)

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
                = Apply () (mapFun Left Plc.sum)
                . Apply () (TyInst () (Builtin () $ Right IdFInteger) Plc.listTy)
                $ mkIterApp () (mapFun Left Plc.enumFromTo) [one, ten]
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess res)

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
                = Apply () (mapFun Left Plc.sum)
                . Apply () (TyInst () (Builtin () $ Right IdList) integer)
                $ mkIterApp () (mapFun Left Plc.enumFromTo) [one, ten]
        tyAct @?= tyExp
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess res)

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

Basically, since we are either generic over @term@ or, like in the example below, use 'CkValue',
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
                = Apply () (mapFun Left Plc.sum)
                . TyInst () (Apply () (TyInst () (Builtin () $ Right IdRank2) Plc.listTy) Plc.nil)
                $ integer
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess res)

test_Swap :: TestTree
test_Swap =
    testCase "Swap" $ do
        let res = mkConstant @(Bool, Integer) @DefaultUni () (False, 1)
            integerPlc = mkTyBuiltin @Integer ()
            boolPlc    = mkTyBuiltin @Bool    ()
            -- swap {integer} {bool} (1, False)
            term
                = Apply () (mkIterInst () (Builtin () $ Right Swap) [integerPlc, boolPlc])
                $ mkConstant @(Integer, Bool) () (1, False)
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess res)

test_definition :: TestTree
test_definition =
    testGroup "definition"
        [ test_Factorial
        , test_Const
        , test_Id
        , test_IdFInteger
        , test_IdList
        , test_IdRank2
        , test_Swap
        ]

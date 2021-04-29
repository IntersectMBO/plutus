-- | A dynamic built-in name test.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.DynamicBuiltins.Definition
    ( test_definition
    ) where

import           PlutusCore
import           PlutusCore.Constant
import           PlutusCore.Generators.Interesting
import           PlutusCore.MkPlc                  hiding (error, unwrap)

import           PlutusCore.Examples.Builtins
import           PlutusCore.StdLib.Data.Bool
import           PlutusCore.StdLib.Data.Function   (fix)
import qualified PlutusCore.StdLib.Data.Function   as Plc
import           PlutusCore.StdLib.Data.Integer    (integer)
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
            -- sum (idRank2 {list} nil {integer})
            term
                = Apply () (mapFun Left Plc.sum)
                . TyInst () (Apply () (TyInst () (Builtin () $ Right IdRank2) Plc.listTy) Plc.nil)
                $ integer
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess res)

-- | Pattern matching on built-in lists. @caseBuiltinList {a} xs@ on built-in lists is
-- equivalent to @unwrap xs@ on lists defined in PLC itself (hence why we bind @r@ after @xs@).
--
-- > /\(a :: *) -> \(xs : [a]) -> /\(r :: *) -> (z : r) (f : a -> [a] -> r) ->
-- >     ifThenElse
-- >         {r}
-- >         (Null {a} xs)
-- >         (\(u : ()) -> z)
-- >         (\(u : ()) -> f (Head {a} xs) (Tail {a} xs))
caseBuiltinList :: Term TyName Name DefaultUni (Either DefaultFun ExtensionFun) ()
caseBuiltinList = runQuote $ do
    a <- freshTyName "a"
    r <- freshTyName "r"
    xs <- freshName "x"
    z <- freshName "z"
    f <- freshName "f"
    u <- freshName "u"
    let listA = TyApp () (mkTyBuiltin @_ @[] ()) $ TyVar () a
        unit = mkTyBuiltin @_ @() ()
        funAtXs fun = apply () (tyInst () (builtin () $ Right fun) $ TyVar () a) $ var () xs
    return
        . tyAbs () a (Type ())
        . lamAbs () xs listA
        . tyAbs () r (Type ())
        . lamAbs () z (TyVar () r)
        . lamAbs () f (TyFun () (TyVar () a) . TyFun () listA $ TyVar () r)
        $ mkIterApp () (tyInst () (mapFun Left ifThenElse) $ TyVar () r)
            [ funAtXs Null
            , lamAbs () u unit $ var () z
            , lamAbs () u unit $ mkIterApp () (var () f) [funAtXs Head, funAtXs Tail]
            ]

-- |  @foldr@ over built-in lists.
--
-- > /\(a :: *) (r :: *) -> \(f : a -> r -> r) (z : r) ->
-- >     fix {[a]} {r} \(rec : [a] -> r) (xs : [a]) ->
-- >         caseBuiltinList {a} xs {r} z \(x : a) (xs' : [a]) -> f x (rec xs')
foldrBuiltinList :: Term TyName Name DefaultUni (Either DefaultFun ExtensionFun) ()
foldrBuiltinList = runQuote $ do
    a   <- freshTyName "a"
    r   <- freshTyName "r"
    f   <- freshName "f"
    z   <- freshName "z"
    rec <- freshName "rec"
    xs  <- freshName "xs"
    x   <- freshName "x"
    xs' <- freshName "xs'"
    let listA = TyApp () (mkTyBuiltin @_ @[] ()) $ TyVar () a
        unwrap ann = apply ann . tyInst () caseBuiltinList $ TyVar () a
    -- Copypasted verbatim from @foldrList@ from the PLC stdlib.
    return
        . tyAbs () a (Type ())
        . tyAbs () r (Type ())
        . lamAbs () f (TyFun () (TyVar () a) . TyFun () (TyVar () r) $ TyVar () r)
        . lamAbs () z (TyVar () r)
        . apply () (mkIterInst () fix [listA, TyVar () r])
        . lamAbs () rec (TyFun () listA $ TyVar () r)
        . lamAbs () xs listA
        . apply () (apply () (tyInst () (unwrap () (var () xs)) $ TyVar () r) $ var () z)
        . lamAbs () x (TyVar () a)
        . lamAbs () xs' listA
        $ mkIterApp () (var () f)
          [ var () x
          , apply () (var () rec) $ var () xs'
          ]

-- | Test that @Null@, @Head@ and @Tail@ are enough to get pattern matching on built-in lists.
test_List :: TestTree
test_List =
    testCase "List" $ do
        let xs  = [1..10]
            res = mkConstant @Integer @DefaultUni () $ foldr (-) 0 xs
            term
                = mkIterApp () (mkIterInst () foldrBuiltinList [integer, integer])
                    [ Builtin () $ Left SubtractInteger
                    , mkConstant @Integer () 0
                    , mkConstant @[Integer] () xs
                    ]
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt term @?= Right (EvaluationSuccess res)

test_Tuple :: TestTree
test_Tuple =
    testCase "Tuple" $ do
        let arg = mkConstant @(Integer, Bool) @DefaultUni () (1, False)
            inst fun = mkIterInst () (Builtin () $ Right fun) [integer, bool]
            swapped = Apply () (inst Swap) arg
            fsted   = Apply () (inst Fst) arg
            snded   = Apply () (inst Snd) arg
        -- Swap {integer} {bool} (1, False) ~> (False, 1)
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt swapped @?=
            Right (EvaluationSuccess $ mkConstant @(Bool, Integer) () (False, 1))
        -- Fst {integer} {bool} (1, False) ~> 1
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt fsted @?=
            Right (EvaluationSuccess $ mkConstant @Integer () 1)
        -- Snd {integer} {bool} (1, False) ~> False
        typecheckEvaluateCkNoEmit defBuiltinsRuntimeExt snded @?=
            Right (EvaluationSuccess $ mkConstant @Bool () False)

-- | Test that @Null@, @Head@ and @Tail@ are enough to get pattern matching on built-in lists.
test_SwapEls :: TestTree
test_SwapEls =
    testCase "SwapEls" $ do
        let xs = zip [1..10] $ cycle [False, True]
            res = mkConstant @Integer @DefaultUni () $
                    foldr (\p r -> r + (if snd p then -1 else 1) * fst p) 0 xs
            el = mkTyBuiltin @_ @(Integer, Bool) ()
            instProj proj = mkIterInst () (builtin () $ Right proj) [integer, bool]
            fun = runQuote $ do
                    p <- freshName "p"
                    r <- freshName "r"
                    return
                        . LamAbs () p el
                        . LamAbs () r integer
                        $ mkIterApp () (builtin () $ Left AddInteger)
                            [ Var () r
                            , mkIterApp () (builtin () $ Left MultiplyInteger)
                                [ mkIterApp () (tyInst () (builtin () $ Left IfThenElse) integer)
                                    [ apply () (instProj Snd) $ Var () p
                                    , mkConstant @Integer () (-1)
                                    , mkConstant @Integer () 1
                                    ]
                                , apply () (instProj Fst) $ Var () p
                                ]
                            ]
            term
                = mkIterApp () (mkIterInst () foldrBuiltinList [el, integer])
                    [ fun
                    , mkConstant @Integer () 0
                    , mkConstant () xs
                    ]
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
        , test_List
        , test_Tuple
        , test_SwapEls
        ]

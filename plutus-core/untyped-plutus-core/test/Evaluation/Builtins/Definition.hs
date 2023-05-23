-- editorconfig-checker-disable-file
-- | Tests for all kinds of built-in functions.

{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}


-- Sure GHC, I'm enabling the extension just so that you can warn me about its usages.
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Evaluation.Builtins.Definition
    ( test_definition
    ) where

import PlutusCore hiding (Constr)
import PlutusCore.Builtin
import PlutusCore.Compiler.Erase (eraseTerm)
import PlutusCore.Data
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Generators.Hedgehog.Interesting
import PlutusCore.MkPlc hiding (error)
import PlutusCore.Pretty
import PlutusPrelude
import UntypedPlutusCore.Evaluation.Machine.Cek

import PlutusCore.Examples.Builtins
import PlutusCore.Examples.Data.Data
import PlutusCore.StdLib.Data.Bool
import PlutusCore.StdLib.Data.Data
import PlutusCore.StdLib.Data.Function qualified as Plc
import PlutusCore.StdLib.Data.Integer
import PlutusCore.StdLib.Data.List qualified as Builtin
import PlutusCore.StdLib.Data.Pair
import PlutusCore.StdLib.Data.ScottList qualified as Scott
import PlutusCore.StdLib.Data.ScottUnit qualified as Scott
import PlutusCore.StdLib.Data.Unit

import Evaluation.Builtins.Common
import Evaluation.Builtins.SignatureVerification (ecdsaSecp256k1Prop, ed25519_V1Prop,
                                                  ed25519_V2Prop, schnorrSecp256k1Prop)

import Control.Exception
import Data.ByteString (ByteString)
import Data.DList qualified as DList
import Data.Proxy
import Data.Text (Text)
import Hedgehog hiding (Opaque, Size, Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

type DefaultFunExt = Either DefaultFun ExtensionFun

defaultBuiltinCostModelExt :: CostingPart DefaultUni DefaultFunExt
defaultBuiltinCostModelExt = (defaultBuiltinCostModel, ())

-- | Check that the 'Factorial' builtin computes to the same thing as factorial defined in PLC
-- itself.
test_Factorial :: TestTree
test_Factorial =
    testCase "Factorial" $ do
        let ten = mkConstant @Integer @DefaultUni () 10
            lhs = typecheckEvaluateCek def defaultBuiltinCostModelExt $
                    apply () (builtin () $ Right Factorial) ten
            rhs = typecheckEvaluateCek def defaultBuiltinCostModelExt $
                    apply () (mapFun Left factorial) ten
        assertBool "type checks" $ isRight lhs
        lhs @?= rhs

-- | Check that 'Const' from the above computes to the same thing as
-- a const defined in PLC itself.
test_Const :: TestTree
test_Const =
    testPropertyNamed "Const" "Const" . property $ do
        c <- forAll $ Gen.text (Range.linear 0 100) Gen.unicode
        b <- forAll Gen.bool
        let tC = mkConstant () c
            tB = mkConstant () b
            text = toTypeAst @_ @DefaultUni @Text Proxy
            runConst con = mkIterAppNoAnn (mkIterInstNoAnn con [text, bool]) [tC, tB]
            lhs = typecheckReadKnownCek def defaultBuiltinCostModelExt $ runConst $ builtin () (Right Const)
            rhs = typecheckReadKnownCek def defaultBuiltinCostModelExt $ runConst $ mapFun @DefaultFun Left Plc.const
        lhs === Right (Right c)
        lhs === rhs

-- | Test that forcing a builtin accepting one type argument and no term arguments makes the
-- builtin compute properly.
test_ForallFortyTwo :: TestTree
test_ForallFortyTwo =
    testCase "ForallFortyTwo" $ do
        let term = tyInst () (builtin () ForallFortyTwo) $ mkTyBuiltin @_ @() ()
            lhs = typecheckEvaluateCekNoEmit def () term
            rhs = Right $ EvaluationSuccess $ mkConstant @Integer () 42
        lhs @?= rhs

-- | Test that a polymorphic built-in function doesn't subvert the CEK machine.
-- See https://github.com/input-output-hk/plutus/issues/1882
test_Id :: TestTree
test_Id =
    testCase "Id" $ do
        let zer = mkConstant @Integer @DefaultUni @DefaultFunExt () 0
            oneT = mkConstant @Integer @DefaultUni () 1
            oneU = mkConstant @Integer @DefaultUni () 1
            -- > id {integer -> integer} ((\(i : integer) (j : integer) -> i) 1) 0
            term =
                mkIterAppNoAnn (tyInst () (builtin () $ Right Id) (TyFun () integer integer))
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
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term @?= Right (EvaluationSuccess oneU)

-- | Test that a polymorphic built-in function can have a higher-kinded type variable in its
-- signature.
test_IdFInteger :: TestTree
test_IdFInteger =
    testCase "IdFInteger" $ do
        let one = mkConstant @Integer @DefaultUni () 1
            ten = mkConstant @Integer @DefaultUni () 10
            res = mkConstant @Integer @DefaultUni () 55
            -- > sum (idFInteger {list} (enumFromTo 1 10))
            term
                = apply () (mapFun Left Scott.sum)
                . apply () (tyInst () (builtin () $ Right IdFInteger) Scott.listTy)
                $ mkIterAppNoAnn (mapFun Left Scott.enumFromTo) [one, ten]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term @?= Right (EvaluationSuccess res)

test_IdList :: TestTree
test_IdList =
    testCase "IdList" $ do
        let tyAct = typeOfBuiltinFunction @DefaultUni def IdList
            tyExp = let a = TyName . Name "a" $ Unique 0
                        listA = TyApp () Scott.listTy (TyVar () a)
                    in TyForall () a (Type ()) $ TyFun () listA listA
            one = mkConstant @Integer @DefaultUni () 1
            ten = mkConstant @Integer @DefaultUni () 10
            res = mkConstant @Integer @DefaultUni () 55
            -- > sum (idList {integer} (enumFromTo 1 10))
            term
                = apply () (mapFun Left Scott.sum)
                . apply () (tyInst () (builtin () $ Right IdList) integer)
                $ mkIterAppNoAnn (mapFun Left Scott.enumFromTo) [one, ten]
        tyAct @?= tyExp
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term @?= Right (EvaluationSuccess res)

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
            -- > sum (idRank2 {list} nil {integer})
            term
                = apply () (mapFun Left Scott.sum)
                . tyInst () (apply () (tyInst () (builtin () $ Right IdRank2) Scott.listTy) Scott.nil)
                $ integer
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term @?= Right (EvaluationSuccess res)

-- | Test that a builtin can be applied to a non-constant term.
test_ScottToMetaUnit :: TestTree
test_ScottToMetaUnit =
    testCase "ScottToMetaUnit" $ do
        let res = EvaluationSuccess $ mkConstant @() @DefaultUni () ()
            applyTerm = apply () (builtin () ScottToMetaUnit)
        -- @scottToMetaUnit Scott.unitval@ is well-typed and runs successfully.
        typecheckEvaluateCekNoEmit def () (applyTerm Scott.unitval) @?= Right res
        let runtime = mkMachineParameters def $ CostModel defaultCekMachineCosts ()
        -- @scottToMetaUnit Scott.map@ is ill-typed, but still runs successfully, since the builtin
        -- doesn't look at the argument.
        unsafeEvaluateCekNoEmit runtime (eraseTerm $ applyTerm Scott.map) @?= res

-- | Test that an exception thrown in the builtin application code does not get caught in the CEK
-- machine and blows in the caller face instead. Uses a one-argument built-in function.
test_FailingSucc :: TestTree
test_FailingSucc =
    testCase "FailingSucc" $ do
        let term =
                apply () (builtin () $ Right FailingSucc) $
                    mkConstant @Integer @DefaultUni @DefaultFunExt () 0
        typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
            -- Here we rely on 'typecheckAnd' lazily running the action after type checking the term.
            traverse (try . evaluate) $ typecheckEvaluateCek def defaultBuiltinCostModelExt term
        typeErrOrEvalExcOrRes @?= Right (Left BuiltinErrorCall)

-- | Test that evaluating a PLC builtin application that is expensive enough to exceed the budget
-- does not result in actual evaluation of the application on the Haskell side and instead we get an
-- 'EvaluationFailure'. Uses a one-argument built-in function.
test_ExpensiveSucc :: TestTree
test_ExpensiveSucc =
    testCase "ExpensiveSucc" $ do
        let term =
                apply () (builtin () $ Right ExpensiveSucc) $
                    mkConstant @Integer @DefaultUni @DefaultFunExt () 0
        typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
            traverse (try . evaluate) $ typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
        typeErrOrEvalExcOrRes @?= Right (Right EvaluationFailure)

-- | Test that an exception thrown in the builtin application code does not get caught in the CEK
-- machine and blows in the caller face instead. Uses a two-arguments built-in function.
test_FailingPlus :: TestTree
test_FailingPlus =
    testCase "FailingPlus" $ do
        let term =
                mkIterAppNoAnn (builtin () $ Right FailingPlus)
                    [ mkConstant @Integer @DefaultUni @DefaultFunExt () 0
                    , mkConstant @Integer @DefaultUni () 1
                    ]
        typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
            -- Here we rely on 'typecheckAnd' lazily running the action after type checking the term.
            traverse (try . evaluate) $ typecheckEvaluateCek def defaultBuiltinCostModelExt term
        typeErrOrEvalExcOrRes @?= Right (Left BuiltinErrorCall)

-- | Test that evaluating a PLC builtin application that is expensive enough to exceed the budget
-- does not result in actual evaluation of the application on the Haskell side and instead we get an
-- 'EvaluationFailure'. Uses a two-arguments built-in function.
test_ExpensivePlus :: TestTree
test_ExpensivePlus =
    testCase "ExpensivePlus" $ do
        let term =
                mkIterAppNoAnn (builtin () $ Right ExpensivePlus)
                    [ mkConstant @Integer @DefaultUni @DefaultFunExt () 0
                    , mkConstant @Integer @DefaultUni () 1
                    ]
        typeErrOrEvalExcOrRes :: Either _ (Either BuiltinErrorCall _) <-
            traverse (try . evaluate) $ typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term
        typeErrOrEvalExcOrRes @?= Right (Right EvaluationFailure)

-- | Test that @Null@, @Head@ and @Tail@ are enough to get pattern matching on built-in lists.
test_BuiltinList :: TestTree
test_BuiltinList =
    testCase "BuiltinList" $ do
        let xs  = [1..10]
            res = mkConstant @Integer @DefaultUni () $ foldr (-) 0 xs
            term
                = mkIterAppNoAnn (mkIterInstNoAnn Builtin.foldrList [integer, integer])
                    [ Builtin () SubtractInteger
                    , mkConstant @Integer () 0
                    , mkConstant @[Integer] () xs
                    ]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModel term @?= Right (EvaluationSuccess res)

-- | Test that right-folding a built-in list with built-in 'Cons' recreates that list.
test_IdBuiltinList :: TestTree
test_IdBuiltinList =
    testCase "IdBuiltinList" $ do
        let xsTerm :: TermLike term tyname name DefaultUni DefaultFunExt => term ()
            xsTerm = mkConstant @[Integer] () [1..10]
            listOfInteger = mkTyBuiltin @_ @[Integer] ()
            term
                = mkIterAppNoAnn (mkIterInstNoAnn (mapFun Left Builtin.foldrList) [integer, listOfInteger])
                    [ tyInst () (builtin () $ Left MkCons) integer
                    , mkConstant @[Integer] () []
                    , xsTerm
                    ]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term @?= Right (EvaluationSuccess xsTerm)

test_BuiltinPair :: TestTree
test_BuiltinPair =
    testCase "BuiltinPair" $ do
        let arg = mkConstant @(Integer, Bool) @DefaultUni () (1, False)
            inst efun = mkIterInstNoAnn (builtin () efun) [integer, bool]
            swapped = apply () (inst $ Right Swap) arg
            fsted   = apply () (inst $ Left FstPair) arg
            snded   = apply () (inst $ Left SndPair) arg
        -- > swap {integer} {bool} (1, False) ~> (False, 1)
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt swapped @?=
            Right (EvaluationSuccess $ mkConstant @(Bool, Integer) () (False, 1))
        -- > fst {integer} {bool} (1, False) ~> 1
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt fsted @?=
            Right (EvaluationSuccess $ mkConstant @Integer () 1)
        -- > snd {integer} {bool} (1, False) ~> False
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt snded @?=
            Right (EvaluationSuccess $ mkConstant @Bool () False)

test_SwapEls :: TestTree
test_SwapEls =
    testCase "SwapEls" $ do
        let xs = zip [1..10] $ cycle [False, True]
            res = mkConstant @Integer @DefaultUni () $
                    foldr (\p r -> r + (if snd p then -1 else 1) * fst p) 0 xs
            el = mkTyBuiltin @_ @(Integer, Bool) ()
            instProj p = mkIterInstNoAnn (builtin () p) [integer, bool]
            fun = runQuote $ do
                    p <- freshName "p"
                    r <- freshName "r"
                    return
                        . lamAbs () p el
                        . lamAbs () r integer
                        $ mkIterAppNoAnn (builtin () AddInteger)
                            [ Var () r
                            , mkIterAppNoAnn (builtin () MultiplyInteger)
                                [ mkIterAppNoAnn (tyInst () (builtin () IfThenElse) integer)
                                    [ apply () (instProj SndPair) $ Var () p
                                    , mkConstant @Integer () (-1)
                                    , mkConstant @Integer () 1
                                    ]
                                , apply () (instProj FstPair) $ Var () p
                                ]
                            ]
            term
                = mkIterAppNoAnn (mkIterInstNoAnn Builtin.foldrList [el, integer])
                    [ fun
                    , mkConstant @Integer () 0
                    , mkConstant () xs
                    ]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModel term @?= Right (EvaluationSuccess res)

-- | Test that right-folding a built-in 'Data' with the constructors of 'Data' recreates the
-- original value.
test_IdBuiltinData :: TestTree
test_IdBuiltinData =
    testCase "IdBuiltinData" $ do
        let dTerm :: TermLike term tyname name DefaultUni fun => term ()
            dTerm = mkConstant @Data () $ Map [(I 42, Constr 4 [List [B "abc", Constr 2 []], I 0])]
            emb = builtin () . Left
            term = mkIterAppNoAnn ofoldrData
                [ emb ConstrData
                , emb MapData
                , emb ListData
                , emb IData
                , emb BData
                , dTerm
                ]
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt term @?= Right (EvaluationSuccess dTerm)

-- | For testing how an evaluator instantiated at a particular 'ExBudgetMode' handles the
-- 'TrackCosts' builtin.
test_TrackCostsWith
    :: String -> Int -> (Term TyName Name DefaultUni ExtensionFun () -> IO ()) -> TestTree
test_TrackCostsWith cat len checkTerm =
    testCase ("TrackCosts: " ++ cat) $ do
        let term
                = apply () (builtin () TrackCosts)
                $ mkConstant @Data () (List . replicate len $ I 42)
        checkTerm term

-- | Test that individual budgets are picked up by GC while spending is still ongoing.
test_TrackCostsRestricting :: TestTree
test_TrackCostsRestricting =
    let n = 30000
    in test_TrackCostsWith "restricting" n $ \term ->
        case typecheckReadKnownCek def () term of
            Left err                         -> fail $ displayPlcDef err
            Right (Left err)                 -> fail $ displayPlcDef err
            Right (Right (res :: [Integer])) -> do
                let expected = n `div` 10
                    actual = length res
                    err = concat
                        [ "Too few elements picked up by GC\n"
                        , "Expected at least: " ++ show expected ++ "\n"
                        , "But got: " ++ show actual
                        ]
                assertBool err $ expected < actual

test_TrackCostsRetaining :: TestTree
test_TrackCostsRetaining =
    test_TrackCostsWith "retaining" 10000 $ \term -> do
        let -- An 'ExBudgetMode' that retains all the individual budgets by sticking them into a
            -- 'DList'.
            retaining = monoidalBudgeting $ const DList.singleton
            typecheckAndRunRetainer = typecheckAnd def $ \params term' ->
                let (getRes, budgets) = runCekNoEmit params retaining term'
                in (getRes >>= readKnownSelf, budgets)
        case typecheckAndRunRetainer () term of
            Left err                                  -> fail $ displayPlcDef err
            Right (Left err, _)                       -> fail $ displayPlcDef err
            Right (Right (res :: [Integer]), budgets) -> do
                -- @length budgets@ is for retaining @budgets@ for as long as possible just in case.
                -- @3@ is just for giving us room to handle erratic GC behavior. It really should be
                -- @1@.
                let expected = min 3 (length budgets)
                    actual = length res
                    err = concat
                        [ "Too many elements picked up by GC\n"
                        , "Expected at most: " ++ show expected ++ "\n"
                        , "But got: " ++ show actual
                        ]
                assertBool err $ expected > actual

-- | Test all integer related builtins
test_Integer :: TestTree
test_Integer = testCase "Integer" $ do
    evals @Integer 3 AddInteger [cons @Integer 2, cons @Integer 1]
    evals @Integer 2 SubtractInteger [cons @Integer 100, cons @Integer 98]
    evals @Integer (-2) SubtractInteger [cons @Integer 98, cons @Integer 100]
    evals @Integer 9702 MultiplyInteger [cons @Integer 99, cons @Integer 98]
    evals @Integer (-3) DivideInteger [cons @Integer 99, cons @Integer (-34)]
    evals @Integer (-2) QuotientInteger [cons @Integer 99, cons @Integer (-34)]
    evals @Integer 31 RemainderInteger [cons @Integer 99, cons @Integer (-34)]
    evals @Integer (-3) ModInteger [cons @Integer 99, cons @Integer (-34)]
    evals True LessThanInteger [cons @Integer 30, cons @Integer 4000]
    evals False LessThanInteger [cons @Integer 40, cons @Integer 40]
    evals True LessThanEqualsInteger [cons @Integer 30, cons @Integer 4000]
    evals True LessThanEqualsInteger [cons @Integer 4000, cons @Integer 4000]
    evals False LessThanEqualsInteger [cons @Integer 4001, cons @Integer 4000]
    evals True EqualsInteger [cons @Integer (-101), cons @Integer (-101)]
    evals False EqualsInteger [cons @Integer 0, cons @Integer 1]

-- | Test all string-like builtins
test_String :: TestTree
test_String = testCase "String" $ do
    -- bytestrings
    evals @ByteString "hello world" AppendByteString [cons @ByteString "hello", cons @ByteString " world"]
    evals @ByteString "mpla" AppendByteString [cons @ByteString "", cons @ByteString "mpla"]
    evals False EqualsByteString [cons @ByteString "" , cons @ByteString "mpla"]
    evals True EqualsByteString [cons @ByteString "mpla" , cons @ByteString "mpla"]
    evals True LessThanByteString  [cons @ByteString "" , cons @ByteString "mpla"]

    -- strings
    evals @Text "mpla" AppendString [cons @Text "", cons @Text "mpla"]
    evals False EqualsString [cons @Text "" , cons @Text "mpla"]
    evals True EqualsString [cons @Text "mpla" , cons @Text "mpla"]
    evals @Text "hello world" AppendString [cons @Text "hello", cons @Text " world"]

    -- id for subset char8 of utf8
    evals @ByteString "hello world" EncodeUtf8 [cons @Text "hello world"]
    evals @Text "hello world" DecodeUtf8 [cons @ByteString "hello world"]

    -- the 'o's replaced with greek o's, so they are kind of "invisible"
    evals @ByteString "hell\206\191 w\206\191rld" EncodeUtf8 [cons @Text "hellο wοrld"]
    -- cannot decode back, because bytestring only works on Char8 subset of utf8
    evals @Text "hellο wοrld" DecodeUtf8 [cons @ByteString "hell\206\191 w\206\191rld"]

    evals @ByteString "\NULhello world" ConsByteString [cons @Integer 0, cons @ByteString "hello world"]
    -- cannot overflow back to 0
    fails ConsByteString [cons @Integer 256, cons @ByteString "hello world"]
    evals @ByteString "\240hello world" ConsByteString [cons @Integer 240, cons @ByteString "hello world"]
    -- 65 is ASCII A
    evals @ByteString "Ahello world" ConsByteString [cons @Integer 65, cons @ByteString "hello world"]

    evals @ByteString "h" SliceByteString [cons @Integer 0, cons @Integer 1, cons @ByteString "hello world"]
    evals @ByteString "he" SliceByteString [cons @Integer 0, cons @Integer 2, cons @ByteString "hello world"]
    evals @ByteString "el" SliceByteString [cons @Integer 1, cons @Integer 2, cons @ByteString "hello world"]
    evals @ByteString "world" SliceByteString [cons @Integer 6, cons @Integer 5, cons @ByteString "hello world"]

    evals @Integer 11 LengthOfByteString [cons @ByteString "hello world"]
    evals @Integer 0 LengthOfByteString [cons @ByteString ""]
    evals @Integer 1 LengthOfByteString [cons @ByteString "\NUL"]

    -- 65 is ASCII A
    evals @Integer 65 IndexByteString [cons @ByteString "Ahello world", cons @Integer 0]
    fails IndexByteString [cons @ByteString "hello world", cons @Integer 12]
    fails IndexByteString [cons @ByteString "", cons @Integer 0]
    fails IndexByteString [cons @ByteString "hello world", cons @Integer 12]

-- | Test all list-related builtins
test_List :: TestTree
test_List = testCase "List" $ do
    evalsL False NullList integer [cons @[Integer] [1,2]]
    evalsL False NullList integer [cons @[Integer] [1]]
    evalsL True NullList integer [cons @[Integer] []]

    evalsL @Integer 1 HeadList integer [cons @[Integer] [1,3]]
    evalsL @[Integer] [3,4,5] TailList integer [cons @[Integer] [1,3,4,5]]

    failsL HeadList integer [cons @[Integer] []]
    failsL TailList integer [cons @[Integer] []]

    evalsL @[Integer] [1] MkCons integer [cons @Integer 1, cons @[Integer] []]
    evalsL @[Integer] [1,2] MkCons integer [cons @Integer 1, cons @[Integer] [2]]

    Right (EvaluationSuccess true)  @=?  typecheckEvaluateCekNoEmit def defaultBuiltinCostModel (nullViaChooseList [])
    Right (EvaluationSuccess false)  @=?  typecheckEvaluateCekNoEmit def defaultBuiltinCostModel (nullViaChooseList [1])
    Right (EvaluationSuccess false)  @=?  typecheckEvaluateCekNoEmit def defaultBuiltinCostModel (nullViaChooseList [1..10])

 where
   evalsL :: Contains DefaultUni a => a -> DefaultFun -> Type TyName DefaultUni () -> [Term TyName Name DefaultUni DefaultFun ()]  -> Assertion
   evalsL expectedVal b tyArg args =
    let actualExp = mkIterAppNoAnn (tyInst () (builtin () b) tyArg) args
    in  Right (EvaluationSuccess $ cons expectedVal)
        @=?
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModel actualExp

   failsL :: DefaultFun -> Type TyName DefaultUni () -> [Term TyName Name DefaultUni DefaultFun ()]  -> Assertion
   failsL b tyArg args =
    let actualExp = mkIterAppNoAnn (tyInst () (builtin () b) tyArg) args
    in  Right EvaluationFailure
        @=?
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModel actualExp

   -- the null function that utilizes the ChooseList builtin (through the caseList helper function)
   nullViaChooseList :: [Integer] -> Term TyName Name DefaultUni DefaultFun ()
   nullViaChooseList l = mkIterAppNoAnn
                      (tyInst () (apply () (tyInst () Builtin.caseList integer) $ cons l) bool)
                      [ -- zero
                        true
                        -- cons
                      , runQuote $ do
                              a1 <- freshName "a1"
                              a2 <- freshName "a2"
                              pure $ lamAbs () a1 integer $ lamAbs () a2 (TyApp () Builtin.list integer) false
                      ]


-- | Test all PlutusData builtins
test_Data :: TestTree
test_Data = testCase "Data" $ do
    -- construction
    evals (Constr 2 [I 3]) ConstrData [cons @Integer 2, cons @[Data] [I 3]]
    evals (Constr 2 [I 3, B ""]) ConstrData [cons @Integer 2, cons @[Data] [I 3, B ""]]
    evals (List []) ListData [cons @[Data] []]
    evals (List [I 3, B ""]) ListData [cons @[Data] [I 3, B ""]]
    evals (Map []) MapData [cons @[(Data,Data)] []]
    evals (Map [(I 3, B "")]) MapData [cons @[(Data,Data)] [(I 3, B "")]]
    evals (B "hello world") BData [cons @ByteString "hello world"]
    evals (I 3) IData [cons @Integer 3]
    evals (B "hello world") BData [cons @ByteString "hello world"]
    evals @[Data] [] MkNilData [cons ()]
    evals @[(Data,Data)] [] MkNilPairData [cons ()]

    -- equality
    evals True EqualsData [cons $ B "hello world", cons $ B "hello world"]
    evals True EqualsData [cons $ I 4, cons $ I 4]
    evals False EqualsData [cons $ B "hello world", cons $ I 4]
    evals True EqualsData [cons $ Constr 3 [I 4], cons $ Constr 3 [I 4]]
    evals False EqualsData [cons $ Constr 3 [I 3, B ""], cons $ Constr 3 [I 3]]
    evals False EqualsData [cons $ Constr 2 [I 4], cons $ Constr 3 [I 4]]
    evals True EqualsData [cons $ Map [(I 3, B "")], cons $ Map [(I 3, B "")]]
    evals False EqualsData [cons $ Map [(I 3, B "")], cons $ Map []]
    evals False EqualsData [cons $ Map [(I 3, B "")], cons $ Map [(I 3, B ""), (I 4, I 4)]]

    -- destruction
    evals @Integer 3 UnIData [cons $ I 3]
    evals @ByteString "hello world" UnBData [cons $ B "hello world"]
    evals @Integer 3 UnIData [cons $ I 3]
    evals @(Integer, [Data]) (1, []) UnConstrData [cons $ Constr 1 []]
    evals @(Integer, [Data]) (1, [I 3]) UnConstrData [cons $ Constr 1 [I 3]]
    evals @[(Data, Data)] [] UnMapData [cons $ Map []]
    evals @[(Data, Data)] [(B "", I 3)] UnMapData [cons $ Map [(B "", I 3)]]
    evals @[Data] [] UnListData [cons $ List []]
    evals @[Data] [I 3, I 4, B ""] UnListData [cons $ List [I 3, I 4, B ""]]
    evals @ByteString "\162\ETX@Ehello8c" SerialiseData [cons $ Map [(I 3, B ""), (B "hello", I $ -100)]]

    -- ChooseData
    let actualExp = mkIterAppNoAnn
                      (tyInst () (apply () caseData $ cons $ I 3) bool)
                      [ -- constr
                        runQuote $ do
                              a1 <- freshName "a1"
                              a2 <- freshName "a2"
                              pure $ lamAbs () a1 integer $ lamAbs () a2 (TyApp () Builtin.list dataTy) false
                        -- map
                      , runQuote $ do
                              a1 <- freshName "a1"
                              pure $ lamAbs () a1 (TyApp () Builtin.list $ mkIterTyApp () pair [dataTy,dataTy]) false
                       -- list
                      , runQuote $ do
                              a1 <- freshName "a1"
                              pure $ lamAbs () a1 (TyApp () Builtin.list dataTy) false
                       -- I
                      , runQuote $ do
                              a1 <- freshName "a1"
                              pure $ lamAbs () a1 integer true
                        -- B
                      , runQuote $ do
                              a1 <- freshName "a1"
                              pure $ lamAbs () a1 (mkTyBuiltin @_ @ByteString ()) false
                      ]

    Right (EvaluationSuccess true)  @=?  typecheckEvaluateCekNoEmit def defaultBuiltinCostModel actualExp

-- | Test all cryptography-related builtins
test_Crypto :: TestTree
test_Crypto = testCase "Crypto" $ do
    evals True VerifyEd25519Signature
        [ -- pubkey
          cons @ByteString "Y\218\215\204>\STX\233\152\251\243\158'm\130\&0\197\DEL\STXd\214`\147\243y(\234\167=kTj\164"
          -- message
        , cons @ByteString "hello world"
          -- signature
        , cons @ByteString "\a'\198\r\226\SYN;\bX\254\228\129n\131\177\193\DC3-k\249RriY\221wIL\240\144\r\145\195\191\196]\227\169U(\ETX\171\SI\199\163\138\160\128R\DC4\246n\142[g\SI\169\SUB\178\245\166\&0\243\b"
        ]

    evals False VerifyEd25519Signature
        [ -- pubkey
          cons @ByteString "Y\218\215\204>\STX\233\152\251\243\158'm\130\&0\197\DEL\STXd\214`\147\243y(\234\167=kTj\164"
          -- message
        , cons @ByteString "HELLO WORLD"
          -- signature
        , cons @ByteString "\a'\198\r\226\SYN;\bX\254\228\129n\131\177\193\DC3-k\249RriY\221wIL\240\144\r\145\195\191\196]\227\169U(\ETX\171\SI\199\163\138\160\128R\DC4\246n\142[g\SI\169\SUB\178\245\166\&0\243\b"
        ]
    -- independently verified by `/usr/bin/sha256sum` with the hex output converted to ascii text
    -- sha256sum hex output: b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9
    evals @ByteString "\185M'\185\147M>\b\165.R\215\218}\171\250\196\132\239\227zS\128\238\144\136\247\172\226\239\205\233"
        Sha2_256 [cons @ByteString "hello world"]
    -- independently verified by `/usr/bin/sha3-256sum` with the hex output converted to ascii text
    -- sha3-256sum hex output: 644bcc7e564373040999aac89e7622f3ca71fba1d972fd94a31c3bfbf24e3938
    evals @ByteString "dK\204~VCs\EOT\t\153\170\200\158v\"\243\202q\251\161\217r\253\148\163\FS;\251\242N98"
        Sha3_256 [cons @ByteString "hello world"]
    -- independently verified by `/usr/bin/b2sum -l 256` with the hex output converted to ascii text
    -- b2sum -l 256 hex output: 256c83b297114d201b30179f3f0ef0cace9783622da5974326b436178aeef610
    evals @ByteString "%l\131\178\151\DC1M \ESC0\ETB\159?\SO\240\202\206\151\131b-\165\151C&\180\&6\ETB\138\238\246\DLE"
        Blake2b_256 [cons @ByteString "hello world"]

-- Test all remaining builtins of the default universe
test_Other :: TestTree
test_Other = testCase "Other" $ do
    let expr1 = mkIterAppNoAnn (tyInst () (builtin () ChooseUnit) bool) [unitval, true]
    Right (EvaluationSuccess true) @=? typecheckEvaluateCekNoEmit def defaultBuiltinCostModel expr1

    let expr2 = mkIterAppNoAnn (tyInst () (builtin () IfThenElse) integer) [true, cons @Integer 1, cons @Integer 0]
    Right (EvaluationSuccess $ cons @Integer 1) @=? typecheckEvaluateCekNoEmit def defaultBuiltinCostModel expr2

    let expr3 = mkIterAppNoAnn (tyInst () (builtin () Trace) integer) [cons @Text "hello world", cons @Integer 1]
    Right (EvaluationSuccess $ cons @Integer 1) @=? typecheckEvaluateCekNoEmit def defaultBuiltinCostModel expr3

-- | Check that 'ExtensionVersion' evaluates correctly.
-- See Note [Versioned builtins]
test_Version :: TestTree
test_Version =
    testCase "Version" $ do
        let expr1 = apply () (builtin () $ Right ExtensionVersion) unitval
        Right (EvaluationSuccess $ cons @Integer 0) @=? typecheckEvaluateCekNoEmit (PairV @DefaultFun def ExtensionFunV0) defaultBuiltinCostModelExt expr1
        Right (EvaluationSuccess $ cons @Integer 1) @=? typecheckEvaluateCekNoEmit (PairV @DefaultFun def def) defaultBuiltinCostModelExt expr1

-- | Check that 'ConsByteString' wraps around for plutus' builtin-version == 1, and fails in plutus's builtin-versions >=2.
-- See Note [Versioned builtins]
test_ConsByteString :: TestTree
test_ConsByteString =
    testCase "ConsVersion" $ do
        let asciiBangWrapped = fromIntegral @Word8 @Integer maxBound
                             + 1 -- to make word8 wraparound
                             + 33 -- the index of '!' in ascii table
            expr1 = mkIterAppNoAnn (builtin () (Left ConsByteString :: DefaultFunExt)) [cons @Integer asciiBangWrapped, cons @ByteString "hello world"]
        Right (EvaluationSuccess $ cons @ByteString "!hello world")  @=? typecheckEvaluateCekNoEmit (PairV DefaultFunV1 def) defaultBuiltinCostModelExt expr1
        Right EvaluationFailure @=? typecheckEvaluateCekNoEmit (PairV DefaultFunV2 def) defaultBuiltinCostModelExt expr1
        Right EvaluationFailure @=? typecheckEvaluateCekNoEmit def defaultBuiltinCostModelExt expr1

-- shorthand
cons :: (Contains DefaultUni a, TermLike term tyname name DefaultUni fun) => a -> term ()
cons = mkConstant ()

-- shorthand
evals :: Contains DefaultUni a => a -> DefaultFun -> [Term TyName Name DefaultUni DefaultFun ()]  -> Assertion
evals expectedVal b args =
    let actualExp = mkIterAppNoAnn (builtin () b) args
    in  Right (EvaluationSuccess $ cons expectedVal)
        @=?
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModel actualExp

-- shorthand
fails :: DefaultFun -> [Term TyName Name DefaultUni DefaultFun ()]  -> Assertion
fails b args =
    let actualExp = mkIterAppNoAnn (builtin () b) args
    in  Right EvaluationFailure
        @=?
        typecheckEvaluateCekNoEmit def defaultBuiltinCostModel actualExp

-- Test that the SECP256k1 builtins are behaving correctly
-- Test that the SECP256k1 builtins are behaving correctly
test_SignatureVerification :: TestTree
test_SignatureVerification =
  adjustOption (\x -> max x . HedgehogTestLimit . Just $ 8000) .
  testGroup "Signature verification" $ [
                 testGroup "Ed25519 signatures (V1)" $ [
                                testPropertyNamed "Ed25519_V1 verification behaves correctly on all inputs" "ed25519_V1_correct" . property $ ed25519_V1Prop
                               ],
                 testGroup "Ed25519 signatures (V2)" $ [
                                testPropertyNamed "Ed25519_V2 verification behaves correctly on all inputs" "ed25519_V2_correct" . property $ ed25519_V2Prop
                               ],
                 testGroup "Signatures on the SECP256k1 curve" $ [
                                testPropertyNamed "ECDSA verification behaves correctly on all inputs" "ecdsa_correct" . property $ ecdsaSecp256k1Prop,
                                testPropertyNamed "Schnorr verification behaves correctly on all inputs" "schnorr_correct" . property $ schnorrSecp256k1Prop
                               ]
                ]
test_definition :: TestTree
test_definition =
    testGroup "definition"
        [ test_Factorial
        , test_ForallFortyTwo
        , test_Const
        , test_Id
        , test_IdFInteger
        , test_IdList
        , test_IdRank2
        , test_ScottToMetaUnit
        , test_FailingSucc
        , test_ExpensiveSucc
        , test_FailingPlus
        , test_ExpensivePlus
        , test_BuiltinList
        , test_IdBuiltinList
        , test_BuiltinPair
        , test_SwapEls
        , test_IdBuiltinData
        , test_TrackCostsRestricting
        , test_TrackCostsRetaining
        , test_Integer
        , test_String
        , test_List
        , test_Data
        , test_Crypto
        , test_SignatureVerification
        , test_Other
        , test_Version
        , test_ConsByteString
        ]

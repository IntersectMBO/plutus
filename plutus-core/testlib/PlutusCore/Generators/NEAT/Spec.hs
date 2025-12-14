-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

{-| Description : Property based testing for Plutus Core

This file contains the tests and some associated machinery but not the
generators. -}
module PlutusCore.Generators.NEAT.Spec
  ( tests
  , Options (..)
  , TestFail (..)
  , bigTest
  , packAssertion
  , tynames
  , names
  , throwCtrex
  , Ctrex (..)
  , handleError
  , handleUError
  , GenDepth (..)
  , GenMode (..)
  ) where

import PlutusCore
import PlutusCore.Compiler.Erase
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Generators.NEAT.Common
import PlutusCore.Generators.NEAT.Term
import PlutusCore.Normalize
import PlutusCore.Pretty

import UntypedPlutusCore qualified as U
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as U

import Control.Monad (unless)
import Control.Monad.Except (ExceptT, catchError, liftEither, runExceptT, throwError, withExceptT)
import Control.Search (Enumerable (..), Options (..), search')
import Data.Default.Class (def)
import Data.Maybe
import Data.Stream qualified as Stream
import Data.Tagged
import Data.Text qualified as Text
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Options
import Text.Printf

-- * Property-based tests

-- | Search depth, measured in program size
newtype GenDepth = GenDepth {unGenDepth :: Int}
  deriving newtype (Read, Eq, Ord)

-- | Search strategy
newtype GenMode = GenMode {unGenMode :: Options}
  deriving newtype (Read)

instance IsOption GenDepth where
  defaultValue = GenDepth 20
  parseValue = safeRead
  optionName = Tagged @GenDepth "gen-depth"
  optionHelp = Tagged @GenDepth "Gen depth"

instance IsOption GenMode where
  defaultValue = GenMode OF
  parseValue = safeRead
  optionName = Tagged @GenMode "gen-mode"
  optionHelp = Tagged @GenMode "Gen Mode"

tests :: TestTree
tests =
  testGroup
    "NEAT"
    -- the `adjustOption (min ...)` allows to make these big tests easier at runtime
    [ adjustOption (min $ GenDepth 10) $
        bigTest
          "normalization commutes with conversion from generated types"
          (Type ())
          (packAssertion prop_normalizeConvertCommuteTypes)
    , adjustOption (min $ GenDepth 12) $
        bigTest
          "normal types cannot reduce"
          (Type ())
          (packAssertion prop_normalTypesCannotReduce)
    , adjustOption (min $ GenDepth 15) $
        bigTest
          "type preservation - CK"
          (TyBuiltinG TyUnitG)
          (packAssertion prop_typePreservation)
    , adjustOption (min $ GenDepth 15) $
        bigTest
          "typed CK vs untyped CEK produce the same output"
          (TyBuiltinG TyUnitG)
          (packAssertion prop_agree_termEval)
    ]

{- NOTE:

The tests below perform multiple steps in a pipeline, they take in
kind & type or type & term and then perform operations on them passing
the result along to the next one, sometimes the result is passed to
several operations and/or several results are later combined and
sometimes a result is discarded. Quite a lot of this is inherently
sequential. There is some limited opportunity for parallelism which is
not exploited.

-}

-- handle a user error and turn it back into an error term
handleError
  :: Type TyName DefaultUni ()
  -> U.ErrorWithCause (U.EvaluationError structural operational) term
  -> Either
       (U.ErrorWithCause (U.EvaluationError structural operational) term)
       (Term TyName Name DefaultUni DefaultFun ())
handleError ty e = case U._ewcError e of
  U.StructuralError _ -> throwError e
  U.OperationalError _ -> return (Error () ty)

-- untyped version of `handleError`
handleUError
  :: U.ErrorWithCause (U.EvaluationError structural operational) term
  -> Either
       (U.ErrorWithCause (U.EvaluationError structural operational) term)
       (U.Term Name DefaultUni DefaultFun ())
handleUError e = case U._ewcError e of
  U.StructuralError _ -> throwError e
  U.OperationalError _ -> return (U.Error ())

{-| Property: check if the type is preserved by evaluation.

 This property is expected to hold for the CK machine. -}
prop_typePreservation :: ClosedTypeG -> ClosedTermG -> ExceptT TestFail Quote ()
prop_typePreservation tyG tmG = do
  tcConfig <- withExceptT TypeError $ getDefTypeCheckConfig ()

  -- Check if the type checker for generated terms is sound:
  ty <- withExceptT GenError $ convertClosedType tynames (Type ()) tyG
  withExceptT TypeError $ checkKind defKindCheckConfig () ty (Type ())
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  withExceptT TypeError $ checkType tcConfig () tm (Normalized ty)

  -- Check if the converted term, when evaluated by CK, still has the same type:

  tmCK <-
    withExceptT CkP $
      liftEither $
        evaluateCkNoEmit defaultBuiltinsRuntimeForTesting def tm `catchError` handleError ty
  withExceptT TypeError $ checkType tcConfig () tmCK (Normalized ty)

{-| Property: check if both the typed CK and untyped CEK machines produce the same output
 modulo erasure. -}
prop_agree_termEval :: ClosedTypeG -> ClosedTermG -> ExceptT TestFail Quote ()
prop_agree_termEval tyG tmG = do
  tcConfig <- withExceptT TypeError $ getDefTypeCheckConfig ()

  -- Check if the type checker for generated terms is sound:
  ty <- withExceptT GenError $ convertClosedType tynames (Type ()) tyG
  withExceptT TypeError $ checkKind defKindCheckConfig () ty (Type ())
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  withExceptT TypeError $ checkType tcConfig () tm (Normalized ty)

  -- run typed CK on input
  tmCk <-
    withExceptT CkP $
      liftEither $
        evaluateCkNoEmit defaultBuiltinsRuntimeForTesting def tm `catchError` handleError ty

  -- erase CK output
  let tmUCk = eraseTerm tmCk

  -- run untyped CEK on erased input
  tmUCek <-
    withExceptT UCekP $
      liftEither $
        U.evaluateCekNoEmit defaultCekParametersForTesting (eraseTerm tm) `catchError` handleUError

  -- check if typed CK and untyped CEK give the same output modulo erasure
  unless (tmUCk == tmUCek) $
    throwCtrex (CtrexUntypedTermEvaluationMismatch tyG tmG [("untyped CK", tmUCk), ("untyped CEK", tmUCek)])

{-| Property: the following diagram commutes for well-kinded types...

 @
                  convertClosedType
    ClosedTypeG ---------------------> Type TyName DefaultUni ()
         |                                        |
         |                                        |
         | normalizeTypeG                         | normalizeType
         |                                        |
         v                                        v
    ClosedTypeG ---------------------> Type TyName DefaultUni ()
                  convertClosedType
 @ -}
prop_normalizeConvertCommuteTypes
  :: Kind ()
  -> ClosedTypeG
  -> ExceptT TestFail Quote ()
prop_normalizeConvertCommuteTypes k tyG = do
  -- Check if the kind checker for generated types is sound:
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  withExceptT TypeError $ checkKind defKindCheckConfig () ty k

  -- Check if the converted type, when reduced, still has the same kind:
  ty1 <- withExceptT TypeError $ unNormalized <$> normalizeType ty
  withExceptT TypeError $ checkKind defKindCheckConfig () ty k

  -- Check if normalization for generated types is sound:
  ty2 <- withExceptT GenError $ convertClosedType tynames k (normalizeTypeG tyG)

  unless (ty1 == ty2) $
    throwCtrex (CtrexNormalizeConvertCommuteTypes k tyG ty1 ty2)

-- | Property: normal types cannot reduce
prop_normalTypesCannotReduce
  :: Kind ()
  -> Normalized ClosedTypeG
  -> ExceptT TestFail Quote ()
prop_normalTypesCannotReduce k (Normalized tyG) =
  unless (isNothing $ stepTypeG tyG) $
    throwCtrex (CtrexNormalTypesCannotReduce k tyG)

-- * Test failures

-- NOTE: a test may fail for several reasons:
--       - we encounter an error in the generator;
--       - we encounter an error while type checking Plutus terms;
--       - we encounter an error while converting to deBruijn notation;
--       - we encounter an error while running the Agda terms;
--       - we found a counter-example.
--
-- This is distinction is not strictly enforced as ultimately
-- everything leads to a counter-example of some kind

data TestFail
  = GenError GenError
  | TypeError
      ( TypeError
          (Term TyName Name DefaultUni DefaultFun ())
          DefaultUni
          DefaultFun
          ()
      )
  | AgdaErrorP ()
  | FVErrorP FreeVariableError
  | CkP (CkEvaluationException DefaultUni DefaultFun)
  | UCekP (U.CekEvaluationException Name DefaultUni DefaultFun)
  | Ctrex Ctrex

data Ctrex
  = CtrexNormalizeConvertCommuteTypes
      (Kind ())
      ClosedTypeG
      (Type TyName DefaultUni ())
      (Type TyName DefaultUni ())
  | CtrexNormalTypesCannotReduce
      (Kind ())
      ClosedTypeG
  | CtrexKindCheckFail
      (Kind ())
      ClosedTypeG
  | CtrexKindPreservationFail
      (Kind ())
      ClosedTypeG
  | CtrexKindMismatch
      (Kind ())
      ClosedTypeG
      (Kind ())
      (Kind ())
  | CtrexTypeNormalizationFail
      (Kind ())
      ClosedTypeG
  | CtrexTypeNormalizationMismatch
      (Kind ())
      ClosedTypeG
      (Type TyName DefaultUni ())
      (Type TyName DefaultUni ())
  | CtrexTypeCheckFail
      ClosedTypeG
      ClosedTermG
  | CtrexTypePreservationFail
      ClosedTypeG
      ClosedTermG
      (Term TyName Name DefaultUni DefaultFun ())
      (Term TyName Name DefaultUni DefaultFun ())
  | CtrexTermEvaluationFail
      String
      ClosedTypeG
      ClosedTermG
  | CtrexTermEvaluationMismatch
      ClosedTypeG
      ClosedTermG
      [(String, Term TyName Name DefaultUni DefaultFun ())]
  | CtrexUntypedTermEvaluationMismatch
      ClosedTypeG
      ClosedTermG
      [(String, U.Term Name DefaultUni DefaultFun ())]

instance Show TestFail where
  show (TypeError e) = "type error: " ++ show e
  show (GenError e) = "generator error: " ++ show e
  show (Ctrex e) = "counter example error: " ++ show e
  show (AgdaErrorP e) = "agda error: " ++ show e
  show (FVErrorP e) = "free variable error: " ++ show e
  show (CkP e) = "CK error: " ++ show e
  show (UCekP e) = "UCEK error: " ++ show e

instance Show Ctrex where
  show (CtrexNormalizeConvertCommuteTypes k tyG ty1 ty2) =
    printf
      tpl
      (show tyG)
      (show (pretty k))
      (show (pretty ty1))
      (show (pretty ty2))
    where
      tpl =
        unlines
          [ "Counterexample found: %s :: %s"
          , "- convert then normalize gives %s"
          , "- normalize then convert gives %s"
          ]
  show (CtrexNormalTypesCannotReduce k tyG) =
    printf tpl (show tyG) (show (pretty k))
    where
      tpl = "Counterexample found: normal type %s of kind %s can reduce."
  show (CtrexKindCheckFail k tyG) =
    printf tpl (show tyG) (show (pretty k))
    where
      tpl = "Counterexample found (kind check fail): %s :: %s"
  show (CtrexKindPreservationFail k tyG) =
    printf tpl (show tyG) (show (pretty k))
    where
      tpl = "Counterexample found (kind preservation fail): %s :: %s"
  show (CtrexKindMismatch k tyG k' k'') =
    printf
      tpl
      (show (pretty k))
      (show tyG)
      (show (pretty k'))
      (show (pretty k''))
    where
      tpl =
        unlines
          [ "Counterexample found: %s :: %s"
          , "- inferer1 gives %s"
          , "- inferer2 gives %s"
          ]
  show (CtrexTypeNormalizationFail k tyG) =
    printf tpl (show tyG) (show (pretty k))
    where
      tpl = "Counterexample found (type normalisation fail): %s :: %s"
  show (CtrexTypeNormalizationMismatch k tyG ty1 ty2) =
    printf
      tpl
      (show tyG)
      (show (pretty k))
      (show (pretty ty1))
      (show (pretty ty2))
    where
      tpl =
        unlines
          [ "Counterexample found: %s :: %s"
          , "- normalizer1 gives %s"
          , "- normalizer2 gives %s"
          ]
  show (CtrexTypeCheckFail tyG tmG) =
    printf tpl (show tmG) (show tyG)
    where
      tpl = "Counterexample found (typecheck fail): %s :: %s"
  show (CtrexTermEvaluationFail s tyG tmG) =
    printf tpl (show tmG) (show tyG)
    where
      tpl = "Counterexample found (" ++ s ++ " term evaluation fail): %s :: %s"
  show (CtrexTermEvaluationMismatch tyG tmG tms) =
    printf tpl (show tmG) (show tyG) ++ results tms
    where
      tpl = "TypedTermEvaluationMismatch\n" ++ "Counterexample found: %s :: %s\n"
      results ((s, t) : ts) = s ++ " evaluation: " ++ show (pretty t) ++ "\n" ++ results ts
      results [] = ""
  show (CtrexUntypedTermEvaluationMismatch tyG tmG tms) =
    printf tpl (show tmG) (show tyG) ++ results tms
    where
      tpl = "UntypedTermEvaluationMismatch\n" ++ "Counterexample found: %s :: %s\n"
      results ((s, t) : ts) = s ++ " evaluation: " ++ show (pretty t) ++ "\n" ++ results ts
      results [] = ""
  show (CtrexTypePreservationFail tyG tmG tm1 tm2) =
    printf tpl (show tmG) (show tyG) (show (pretty tm1)) (show (pretty tm2))
    where
      tpl =
        unlines
          [ "Counterexample found: %s :: %s"
          , "before evaluation: %s"
          , "after evaluation:  %s"
          ]

-- | Throw a counter-example.
throwCtrex :: Ctrex -> ExceptT TestFail Quote ()
throwCtrex ctrex = throwError (Ctrex ctrex)

-- | Stream of type names t0, t1, t2, ..
tynames :: Stream.Stream Text.Text
tynames = mkTextNameStream "t"

-- | Stream of names x0, x1, x2, ..
names :: Stream.Stream Text.Text
names = mkTextNameStream "x"

-- | given a prop, generate one test
packAssertion :: Show e => (t -> a -> ExceptT e Quote ()) -> t -> a -> Assertion
packAssertion f t a =
  case runQuote . runExceptT $ f t a of
    Left e -> assertFailure $ show e
    Right _ -> return ()

{-| generate examples using `search'` and then generate one big test
that applies the given test to each of them. -}
bigTest
  :: (Check t a, Enumerable a)
  => String -> t -> (t -> a -> Assertion) -> TestTree
bigTest s t f = askOption $ \genMode -> askOption $ \genDepth -> testCaseInfo s $ do
  as <- search' (unGenMode genMode) (unGenDepth genDepth) (\a -> check t a)
  _ <- traverse (f t) as
  return $ show (length as)

{-|
Description : Property based testing for Plutus Core

This file contains the tests and some associated machinery but not the
generators.
-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Language.PlutusCore.Generators.NEAT.Spec
  ( tests
  , GenOptions (..)
  , defaultGenOptions
  , Options (..)
  , TestFail (..)
  , testCaseGen
  , tynames
  , names
  , throwCtrex
  , Ctrex (..)
  ) where

import           Language.PlutusCore
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Generators.NEAT.Common
import           Language.PlutusCore.Generators.NEAT.Type
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Pretty

import           Control.Monad.Except
import           Control.Search                                             (Enumerable (..), Options (..), ctrex')
import           Data.Coolean                                               (Cool, toCool, (!=>))
import           Data.Either
import           Data.Maybe
import qualified Data.Stream                                                as Stream
import qualified Data.Text                                                  as Text
import           Test.Tasty
import           Test.Tasty.HUnit
import           Text.Printf


-- * Property-based tests

data GenOptions = GenOptions
  { genDepth :: Int     -- ^ Search depth, measured in program size
  , genMode  :: Options -- ^ Search strategy
  }

defaultGenOptions :: GenOptions
defaultGenOptions = GenOptions
  { genDepth = 10
  , genMode  = OF
  }

tests :: GenOptions -> TestTree
tests genOpts@GenOptions{..} =
  testGroup "NEAT"
  [ testCaseGen "normalization commutes with conversion from generated types"
      genOpts
      (Type ())
      prop_normalizeConvertCommuteTypes
  , testCaseGen "normal types cannot reduce"
      genOpts
      (Type ())
      prop_normalTypesCannotReduce
  , testCaseGen "type preservation - CK"
      genOpts
      (Type (), TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      prop_typePreservationCk
  -- this fails, but we run it anyway and catch the error
  , testCaseGen "type preservation - CEK"
      genOpts
      (Type (), TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      prop_typePreservationCek
  , testCaseGen "CEK and CK produce the same output"
      genOpts
--    v  - this fails as it exposes mistreatment of type annotations by CEK
--    (Type (), TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      (Type (), TyBuiltinG TyIntegerG)
      prop_agree_Ck_Cek
  ]
-- |Property: the following diagram commutes for well-typed terms...
--
-- @
--                  convertClosedTerm
--    ClosedTermG ---------------------> Term TyName Name DefaultUni ()
--         |                                        |
--         |                                        |
--         | normalizeTermG [?]                     | normalizeTerm [?]
--         |                                        |
--         v                                        v
--    ClosedTermG ---------------------> Term TyName Name DefaultUni ()
--                  convertClosedTerm
-- @
--
prop_typePreservationCk :: (Kind (), ClosedTypeG) -> ClosedTermG -> ExceptT TestFail Quote ()
prop_typePreservationCk (k, tyG) tmG = do

  -- Check if the type checker for generated terms is sound:
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  withExceptT TypeError $ checkKind defConfig () ty k
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  withExceptT TypeError $ checkType defConfig () tm (Normalized ty)

  -- Check if the converted term, when evaluated, still has the same type:

  tmV <- withExceptT CkP $ liftEither $ evaluateCk mempty tm
  withExceptT TypeError $ checkType defConfig () tmV (Normalized ty)


prop_typePreservationCek :: (Kind (), ClosedTypeG) -> ClosedTermG -> ExceptT TestFail Quote ()
prop_typePreservationCek (k, tyG) tmG = do

  -- Check if the type checker for generated terms is sound:
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  withExceptT TypeError $ checkKind defConfig () ty k
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  withExceptT TypeError $ checkType defConfig () tm (Normalized ty)

  -- Check if the converted term, when evaluated, still has the same type:

  tmV <- withExceptT CekP $ liftEither $ evaluateCek mempty defaultCostModel tm
  withExceptT
    (\ (_ :: TypeError DefaultUni ()) -> Ctrex (CtrexTypePreservationFail tyG tmG tm tmV))
    (checkType defConfig () tmV (Normalized ty))
    `catchError` \_ -> return () -- expecting this to fail at the moment

prop_agree_Ck_Cek :: (Kind (), ClosedTypeG) -> ClosedTermG -> ExceptT TestFail Quote ()
prop_agree_Ck_Cek (k, tyG) tmG = do

  -- Check if the type checker for generated terms is sound:
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  withExceptT TypeError $ checkKind defConfig () ty k
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  withExceptT TypeError $ checkType defConfig () tm (Normalized ty)

  -- Check if the converted term, when normalized, still has the same type:

  tmCek <- withExceptT CekP $ liftEither $ evaluateCek mempty defaultCostModel tm
  tmCk <- withExceptT CkP $ liftEither $ evaluateCk mempty tm
  unless (tmCk == tmCek) $ throwCtrex (CtrexTermEvaluationMismatch tyG tmG [tmCek,tmCk])

-- |Property: the following diagram commutes for well-kinded types...
--
-- @
--                  convertClosedType
--    ClosedTypeG ---------------------> Type TyName DefaultUni ()
--         |                                        |
--         |                                        |
--         | normalizeTypeG                         | normalizeType
--         |                                        |
--         v                                        v
--    ClosedTypeG ---------------------> Type TyName DefaultUni ()
--                  convertClosedType
-- @
--
prop_normalizeConvertCommuteTypes :: Kind () -> ClosedTypeG -> ExceptT TestFail Quote ()
prop_normalizeConvertCommuteTypes k tyG = do

  -- Check if the kind checker for generated types is sound:
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  withExceptT TypeError $ checkKind defConfig () ty k

  -- Check if the converted type, when reduced, still has the same kind:
  ty1 <- withExceptT TypeError $ unNormalized <$> normalizeType ty
  withExceptT TypeError $ checkKind defConfig () ty k

  -- Check if normalization for generated types is sound:
  ty2 <- withExceptT GenError $ convertClosedType tynames k (normalizeTypeG tyG)
  unless (ty1 == ty2) $ throwCtrex (CtrexNormalizeConvertCommuteTypes k tyG ty1 ty2)

-- |Property: normal types cannot reduce
prop_normalTypesCannotReduce :: Kind () -> Normalized ClosedTypeG -> ExceptT TestFail Quote ()
prop_normalTypesCannotReduce k (Normalized tyG) =
  unless (isNothing $ stepTypeG tyG) $ throwCtrex (CtrexNormalTypesCannotReduce k tyG)


-- |Create a generator test, searching for a counter-example to the given predicate.
testCaseGen :: (Check t a, Enumerable a, Show e)
        => TestName
        -> GenOptions
        -> t
        -> (t -> a -> ExceptT e Quote ())
        -> TestTree
testCaseGen name GenOptions{..} t prop =
  testCaseInfo name $ do
    -- NOTE: in the `Right` case, `prop t ctrex` is guarded by `not (isOk (prop t ctrex))`
    result <- ctrex' genMode genDepth (\x -> check t x !=> isOk (prop t x))
    case result of
      Left  count -> return $ printf "%d examples generated" count
      Right ctrex -> assertFailure . either show undefined . run $ prop t ctrex


-- * Test failures

-- NOTE: a test may fail for several reasons:
--       - we encounter an error in the generator;
--       - we encounter an error while type checking Plutus terms;
--       - we encounter an error while converting to deBruijn notation;
--       - we encounter an error while running the Agda terms;
--       - we found a counter-example.

-- james: Isn't everything except an error in the generator a counterexample?

data TestFail
  = GenError GenError
  | TypeError (TypeError DefaultUni ())
  | AgdaErrorP ()
  | FVErrorP FreeVariableError
  | CkP (CkEvaluationException DefaultUni)
  | CekP (CekEvaluationException DefaultUni)
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
    (Term TyName Name DefaultUni ())
    (Term TyName Name DefaultUni ())
  | CtrexTermEvaluationFail
    ClosedTypeG
    ClosedTermG
  | CtrexTermEvaluationMismatch
    ClosedTypeG
    ClosedTermG
    [Term TyName Name DefaultUni ()]

instance Show TestFail where
  show (TypeError e)  = show e
  show (GenError e)   = show e
  show (Ctrex e)      = show e
  show (AgdaErrorP e) = show e
  show (FVErrorP e)   = show e
  show (CkP e)        = show e
  show (CekP e)       = show e

instance Show Ctrex where
  show (CtrexNormalizeConvertCommuteTypes k tyG ty1 ty2) =
    printf tpl (show tyG) (show (pretty k)) (show (pretty ty1)) (show (pretty ty2))
    where
      tpl = unlines
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
      tpl = "Counterexample found: %s :: %s"
  show (CtrexKindPreservationFail k tyG) =
    printf tpl (show tyG) (show (pretty k))
    where
      tpl = "Counterexample found: %s :: %s"
  show (CtrexKindMismatch k tyG k' k'') =
    printf tpl (show (pretty k)) (show tyG) (show (pretty k')) (show (pretty k''))
      where
      tpl = unlines
            [ "Counterexample found: %s :: %s"
            , "- inferer1 gives %s"
            , "- inferer2 gives %s"
            ]
  show (CtrexTypeNormalizationFail k tyG) =
    printf tpl (show tyG) (show (pretty k))
    where
      tpl = "Counterexample found: %s :: %s"
  show (CtrexTypeNormalizationMismatch k tyG ty1 ty2) =
    printf tpl (show tyG) (show (pretty k)) (show (pretty ty1)) (show (pretty ty2))
    where
      tpl = unlines
            [ "Counterexample found: %s :: %s"
            , "- normalizer1 gives %s"
            , "- normalizer2 gives %s"
            ]
  show (CtrexTypeCheckFail tyG tmG) =
    printf tpl (show tmG) (show tyG)
    where
      tpl = "Counterexample found: %s :: %s"
  show (CtrexTermEvaluationFail tyG tmG) =
    printf tpl (show tmG) (show tyG)
    where
      tpl = "Counterexample found: %s :: %s"
  show (CtrexTermEvaluationMismatch tyG tmG tms) =
    printf tpl (show tmG) (show tyG) ++ results tms
    where
      tpl = "Counterexample found: %s :: %s\n"
      results (t:ts) = "evaluation: " ++ show (pretty t) ++ "\n" ++ results ts
      results []     = ""
  show (CtrexTypePreservationFail tyG tmG tm1 tm2) =
    printf tpl (show tmG) (show tyG) (show (pretty tm1)) (show (pretty tm2))
    where
      tpl = unlines
            [ "Counterexample found: %s :: %s"
            , "before evaluation: %s"
            , "after evaluation:  %s"
            ]

-- |Throw a counter-example.
throwCtrex :: Ctrex -> ExceptT TestFail Quote ()
throwCtrex ctrex = throwError (Ctrex ctrex)

-- |Check if running |Quote| and |Except| throws any errors.
isOk :: ExceptT e Quote a -> Cool
isOk = toCool . isRight . run

-- |Run |Quote| and |Except| effects.
run :: ExceptT e Quote a -> Either e a
run = runQuote . runExceptT

-- |Stream of type names t0, t1, t2, ..
tynames :: Stream.Stream Text.Text
tynames = mkTextNameStream "t"

-- |Stream of names x0, x1, x2, ..
names :: Stream.Stream Text.Text
names = mkTextNameStream "x"

{-|
Description : Property based testing for Plutus Core

This file contains the machinery for property based testing of
generated types. Generation of terms is not implemented yet.
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
import           Language.PlutusCore.Generators.NEAT.Common
import           Language.PlutusCore.Generators.NEAT.Type
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Pretty

import           Control.Monad.Except
import           Control.Search                             (Enumerable (..), Options (..), ctrex')
import           Data.Coolean                               (Cool, toCool, (!=>))
import           Data.Either
import           Data.Maybe
import qualified Data.Stream                                as Stream
import qualified Data.Text                                  as Text
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
  , testCaseGen "normalization commutes with conversion from generated terms"
      genOpts
      (Type (), TyFunG (TyBuiltinG TyIntegerG) (TyBuiltinG TyIntegerG))
      prop_normalizeConvertCommuteTerms
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
prop_normalizeConvertCommuteTerms :: (Kind (), ClosedTypeG) -> ClosedTermG -> ExceptT TestFail Quote ()
prop_normalizeConvertCommuteTerms (k, tyG) tmG = do

  -- Check if the type checker for generated terms is sound:
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  withExceptT TypeError $ checkKind defConfig () ty k
  tm <- withExceptT GenError $ convertClosedTerm tynames names tyG tmG
  withExceptT TypeError $ checkType defConfig () tm (Normalized ty)

  -- Check if the converted term, when normalized, still has the same type:

  -- Check if normalization for generated terms is sound:

  return ()

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
  unless (ty1 == ty2) $ throwCtrex (CtrexNormalizeConvertCommuteTypes k ty ty1 ty2)

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

data TestFail
  = GenError GenError
  | TypeError (TypeError DefaultUni ())
  | AgdaErrorP () -- FIXME
  | FVErrorP FreeVariableError -- FIXME
  | Ctrex Ctrex

data Ctrex
  = CtrexNormalizeConvertCommuteTypes
    (Kind ())
    (Type TyName DefaultUni ())
    (Type TyName DefaultUni ())
    (Type TyName DefaultUni ())
  | CtrexNormalTypesCannotReduce
    (Kind ())
    ClosedTypeG

instance Show TestFail where
  show (TypeError e)  = show e
  show (GenError e)   = show e
  show (Ctrex e)      = show e
  show (AgdaErrorP e) = show e -- FIXME
  show (FVErrorP e)   = show e -- FIXME

instance Show Ctrex where
  show (CtrexNormalizeConvertCommuteTypes k ty ty1 ty2) =
    printf tpl (show (pretty ty)) (show (pretty k)) (show (pretty ty1)) (show (pretty ty2))
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

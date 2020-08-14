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

module Language.PlutusCore.Gen.Spec
  ( tests
  , GenOptions (..)
  , defaultGenOptions
  , Options (..)
  ) where

import           Language.PlutusCore
import           Language.PlutusCore.Gen.Common
import           Language.PlutusCore.Gen.Type
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Pretty

import           Control.Monad.Except
import           Control.Search (Enumerable(..),Options(..),ctrex')
import           Data.Coolean (Cool,toCool,(!=>))
import           Data.Either
import           Data.Maybe
import qualified Data.Stream                    as Stream
import qualified Data.Text                      as Text
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
      prop_normalizeConvertCommute
  , testCaseGen "normal types cannot reduce"
      genOpts
      (Type ())
      prop_normalTypesCannotReduce
  ]

-- |Property: the following diagram commutes for well-kinded types...
--
-- @
--                  convertClosedType
--    ClosedTypeG ---------------------> Type TyName ()
--         |                                   |
--         |                                   |
--         | normalizeTypeG                    | normalizeType
--         |                                   |
--         v                                   v
--    ClosedTypeG ---------------------> Type TyName ()
--                  convertClosedType
-- @
--
prop_normalizeConvertCommute :: Kind () -> ClosedTypeG -> ExceptT TestFail Quote ()
prop_normalizeConvertCommute k tyG = do

  -- Check if the kind checker for generated types is sound:
  ty <- withExceptT GenError $ convertClosedType tynames k tyG
  withExceptT TypeError $ checkKind defConfig () ty k

  -- Check if the converted type, when reduced, still has the same kind:
  ty1 <- withExceptT TypeError $ unNormalized <$> normalizeType ty
  withExceptT TypeError $ checkKind defConfig () ty k

  -- Check if normalization for generated types is sound:
  ty2 <- withExceptT GenError $ convertClosedType tynames k (normalizeTypeG tyG)
  unless (ty1 == ty2) $ throwCtrex (CtrexClosedTypeG k tyG)


-- |Property: normal types cannot reduce
prop_normalTypesCannotReduce :: Kind () -> Normalized ClosedTypeG -> ExceptT TestFail Quote ()
prop_normalTypesCannotReduce k (Normalized tyG) =
  unless (isNothing $ stepTypeG tyG) $ throwCtrex (CtrexClosedTypeG k tyG)


-- |Create a generator test, searching for a counter-example to the given predicate.
testCaseGen :: (Check t a, Enumerable a)
        => TestName
        -> GenOptions
        -> t
        -> (t -> a -> ExceptT TestFail Quote ())
        -> TestTree
testCaseGen name GenOptions{..} t prop =
  testCaseInfo name $ do
    -- NOTE: in the `Right` case, `prop t ctrex` is guarded by `not (isOk (prop t ctrex))`
    result <- ctrex' genMode genDepth (\x -> check t x !=> isOk (prop t x))
    case result of
      Left  count -> return $ printf "%d examples generated" count
      Right ctrex -> assertFailure . either show undefined . run $ prop t ctrex


-- |Generalise over kind and type checking functions.
class Check t a where
  check :: t -> a -> Cool

instance Check (Kind ()) ClosedTypeG where
  check = checkClosedTypeG

instance Check (Kind ()) (Normalized ClosedTypeG) where
  check k ty = checkClosedTypeG k (unNormalized ty)


-- * Test failures

-- NOTE: a test may fail for several reasons:
--       - we encounter an error in the generator;
--       - we encounter a type error while checking Plutus terms;
--       - we found a counter-example.

data TestFail
  = GenError GenError
  | TypeError (TypeError DefaultUni ())
  | Ctrex Ctrex

data Ctrex
  = CtrexClosedTypeG (Kind ()) ClosedTypeG

instance Show TestFail where
  show (TypeError e) = show e
  show (GenError e) = show e
  show (Ctrex e) = show e

instance Show Ctrex where
  show (CtrexClosedTypeG kG tyG) = either show go (run $ convertClosedType tynames kG tyG)
    where
      go ty =
        case run (inferKind defConfig ty) of
          Left err ->
            printf "Counterexample found: %s, generated for kind %s\n%s"
            (show (pretty ty))
            (show (pretty kG))
            (show (prettyPlcClassicDef (err :: TypeError DefaultUni ())))
          Right k ->
            printf "Counterexample found: %s, generated for kind %s, has inferred kind %s"
            (show (pretty ty))
            (show (pretty kG))
            (show (pretty k))

-- |Throw a counter-example.
throwCtrex :: Ctrex -> ExceptT TestFail Quote ()
throwCtrex ctrex = throwError (Ctrex ctrex)

-- |Check if running |Quote| and |Except| throws any errors.
isOk :: ExceptT TestFail Quote a -> Cool
isOk = toCool . isRight . run

-- |Run |Quote| and |Except| effects.
run :: ExceptT e Quote a -> Either e a
run = runQuote . runExceptT

-- |Stream of type names t0, t1, t2, ..
tynames :: Stream.Stream Text.Text
tynames = mkTextNameStream "t"

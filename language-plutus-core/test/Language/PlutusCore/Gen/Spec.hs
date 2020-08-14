{-|
Description : Property based testing for Plutus Core

This file contains the machinery for property based testing of
generated types. Generation of terms is not implemented yet.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE RecordWildCards   #-}

module Language.PlutusCore.Gen.Spec
  ( tests
  , GenOptions (..)
  , defaultGenOptions
  , NEAT.Options (..)
  ) where

import           Language.PlutusCore
import           Language.PlutusCore.Gen.Common
import           Language.PlutusCore.Gen.Type   hiding (toClosedType)
import qualified Language.PlutusCore.Gen.Type   as Gen
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Pretty

import           Control.Monad.Except
import           Control.Search                 as NEAT
import qualified Data.Coolean                   as Cool
import qualified Data.Either                    as Either
import qualified Data.Stream                    as Stream
import qualified Data.Text                      as Text
import           Test.Tasty
import           Test.Tasty.HUnit
import           Text.Printf


-- * Property-based tests

data GenOptions = GenOptions
  { genDepth :: Int          -- ^ Search depth, measured in program size
  , genKind  :: Kind ()      -- ^ Kind of types to generate
  , genMode  :: NEAT.Options -- ^ Search strategy
  }

defaultGenOptions :: GenOptions
defaultGenOptions = GenOptions
  { genDepth = 10
  , genKind  = Type ()
  , genMode  = NEAT.OF
  }

tests :: GenOptions -> TestTree
tests GenOptions{..} = testGroup "NEAT"
    [ testCaseCount "kind checker for generated types is sound" $
        testTyProp genDepth genKind genMode prop_checkKindSound
    , testCaseCount "normalization preserves kinds" $
        testTyProp genDepth genKind genMode prop_normalizePreservesKind
    , testCaseCount "normalization for generated types is sound" $
        testTyProp genDepth genKind genMode prop_normalizeTypeSound
    ]

-- |Property: Kind checker for generated types is sound.
prop_checkKindSound :: TyProp
prop_checkKindSound k _ tyQ = isSafe $ do
  ty <- withExceptT GenErrorP tyQ
  withExceptT TypeErrorP $ checkKind defConfig () ty k

-- |Property: Normalisation preserves kind.
prop_normalizePreservesKind :: TyProp
prop_normalizePreservesKind k _ tyQ = isSafe $ do
  ty  <- withExceptT GenErrorP tyQ
  ty' <- withExceptT TypeErrorP $ unNormalized <$> normalizeType ty
  withExceptT TypeErrorP $ checkKind defConfig () ty' k

-- |Property: Normalisation for generated types is sound.
prop_normalizeTypeSound :: TyProp
prop_normalizeTypeSound k tyG tyQ = isSafe $ do
  ty <- withExceptT GenErrorP tyQ
  ty1 <- withExceptT TypeErrorP $ unNormalized <$> normalizeType ty
  ty2 <- withExceptT GenErrorP $ toClosedType k (normalizeTypeG tyG)
  return (ty1 == ty2)

-- * Helper functions

-- |The type for properties with access to both representations.
type TyProp =  Kind ()                           -- ^ kind for generated type
            -> ClosedTypeG                       -- ^ generated type
            -> ExceptT GenError Quote (Type TyName DefaultUni ()) -- ^ external rep. of gen. type
            -> Cool                              -- ^ whether the property holds

-- |Internal version of type properties.
type TyPropG =  Kind ()      -- ^ kind of the generated type
             -> ClosedTypeG  -- ^ generated type
             -> Cool         -- ^ whether the property holds


-- |Test property on well-kinded types.
testTyProp :: Int          -- ^ Search depth
           -> Kind ()      -- ^ Kind for generated types
           -> NEAT.Options -- ^ Search mode
           -> TyProp       -- ^ Property to test
           -> IO Integer
testTyProp depth k mode typrop = do
  result <- ctrex' mode depth (toTyPropG typrop k)
  case result of
    Left  i   -> return i
    Right tyG -> assertFailure (errorMsgTyProp k tyG)

-- |Print the number of generated test cases.
testCaseCount :: String -> IO Integer -> TestTree
testCaseCount name act = testCaseInfo name $
  fmap (\i -> show i ++ " types generated") act

-- |Check if the type/kind checker or generation threw any errors.
isSafe :: ExceptT (ErrorP a) Quote a -> Cool
isSafe = Cool.toCool . Either.isRight . runQuote . runExceptT

-- |Generate the error message for a failed `TyProp`.
errorMsgTyProp :: Kind () -> ClosedTypeG -> String
errorMsgTyProp kG tyG =
  case run (toClosedType kG tyG) of
    Left (Gen ty k) ->
      printf "Test generation error: convert type %s at kind %s" (show ty) (show k)
    Right ty ->
      case run (inferKind defConfig ty) of
        Left err ->
          printf "Counterexample found: %s, generated for kind %s\n%s"
            (show (pretty ty)) (show (pretty kG)) (show (prettyPlcClassicDef (err :: TypeError DefaultUni ())))
        Right k2 ->
          printf "Counterexample found: %s, generated for kind %s, has inferred kind %s"
            (show (pretty ty)) (show (pretty kG)) (show (pretty k2))
  where
    run :: ExceptT e Quote a -> Either e a
    run = runQuote . runExceptT

-- |Convert a `TyProp` to the internal representation of types.
toTyPropG :: TyProp -> TyPropG
toTyPropG typrop kG tyG = tyG_ok Cool.!=> typrop_ok
  where
    tyG_ok    = checkClosedTypeG kG tyG
    typrop_ok = typrop kG tyG (toClosedType kG tyG)

-- |Convert type.
toClosedType :: (MonadQuote m, MonadError GenError m)
             => Kind ()
             -> ClosedTypeG
             -> m (Type TyName DefaultUni ())
toClosedType = Gen.toClosedType tynames

-- |Stream of type names t0, t1, t2, ..
tynames :: Stream.Stream Text.Text
tynames = mkTextNameStream "t"

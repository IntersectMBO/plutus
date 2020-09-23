{-|
Description : Property based testing for Plutus Core

This file contains the machinery for property based testing of
generated types. Generation of terms is not implemented yet.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.Generators.NEAT.PropTest
  ( TyProp
  , testTyProp
  , toClosedType
  , normalizeTypeG
  , GenError (..)
  , ErrorP (..)
  ) where

import           Language.PlutusCore
import           Language.PlutusCore.Generators.NEAT.Common
import           Language.PlutusCore.Generators.NEAT.Type   hiding (toClosedType)
import qualified Language.PlutusCore.Generators.NEAT.Type   as Gen
import           Language.PlutusCore.Pretty

import           Control.Monad.Except
import           Control.Search
import qualified Data.Coolean                               as Cool
import qualified Data.Stream                                as Stream
import qualified Data.Text                                  as Text
import           Test.Tasty.HUnit
import           Text.Printf


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
testTyProp :: Int     -- ^ Search depth
           -> Kind () -- ^ Kind for generated types
           -> TyProp  -- ^ Property to test
           -> IO Integer
testTyProp depth k typrop = do
  -- NOTE: Any strategy which attempts fairness will crash the search!
  --       These strategies evaluate !=> in *parallel*, and hence attempt
  --       to convert ill-kinded types, but `toType` is partial!
  -- TODO: This *may* be a bug in the lazy-search library.
  -- UPDATE: toType is nolonger partial
  result <- ctrex' O depth (toTyPropG typrop k)
  case result of
    Left  i   -> return i
    Right tyG -> assertFailure (errorMsgTyProp k tyG)


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
            (show (pretty ty)) (show (pretty kG)) (show (prettyPlcClassicDef (err :: TypeError (Term TyName Name DefaultUni ()) DefaultUni ())))
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

-- |Stream of type names t0, t1, t2, ..
tynames :: Stream.Stream Text.Text
tynames = mkTextNameStream "t"


-- |Convert type.
toClosedType :: (MonadQuote m, MonadError GenError m)
             => Kind ()
             -> ClosedTypeG
             -> m (Type TyName DefaultUni ())
toClosedType = Gen.toClosedType tynames

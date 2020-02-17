{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Language.PlutusCore.PropTest
  ( TyProp
  , testTyProp
  ) where

import           Language.PlutusCore
import           Language.PlutusCore.Gen.Common
import           Language.PlutusCore.Gen.Type
import           Language.PlutusCore.Pretty

import           Control.Search (ctrex', Options (..))
import           Control.Monad.Except

import           Data.Coolean (Cool, (!=>))
import qualified Data.Text as Text
import           Text.Printf


-- |The type for properties on well-kinded PlutusCore types.
type TyProp = Kind () -> Quote (Type TyName ()) -> Cool

-- |Internal version of type properties.
type TyPropG = KindG -> ClosedTypeG -> Cool


-- |Test property on well-kinded types.
testTyProp :: Int      -- ^ Search depth
           -> Kind ann -- ^ Kind for generated types
           -> TyProp   -- ^ Property to test
           -> IO ()
testTyProp depth k typrop = do
  -- NOTE: Any strategy which attempts fairness will crash the search!
  --       These strategies evaluate !=> in *parallel*, and hence attempt
  --       to convert ill-kinded types, but `toType` is partial!
  -- TODO: This *may* be a bug in the lazy-search library.
  let kG = fromKind k
  result <- ctrex' OS depth (toTyPropG typrop kG)
  case result of
    Left  _   -> return ()
    Right tyG -> error (errorMsgTyProp kG tyG)


-- |Generate the error message for a failed `TyProp`.
errorMsgTyProp :: KindG -> ClosedTypeG -> String
errorMsgTyProp kG tyG =
  case run (inferKind defOffChainConfig =<< liftQuote tyQ) of
    Left err ->
      printf "Counterexample found: %s, generated for kind %s\n%s"
        (show (pretty ty)) (show (pretty k1)) (show (prettyPlcClassicDef err))
    Right k2 ->
      printf "Counterexample found: %s, generated for kind %s, has inferred kind %s"
        (show (pretty ty)) (show (pretty k1)) (show (pretty k2))
  where
    run :: ExceptT (TypeError ()) Quote a -> Either (TypeError ()) a
    run = runQuote . runExceptT

    tyQ = toClosedType tynames kG tyG :: Quote (Type TyName ())
    ty  = runQuote tyQ                :: Type TyName ()
    k1  = toKind kG                   :: Kind ()


-- |Convert a `TyProp` to the internal representation of types.
toTyPropG :: TyProp -> TyPropG
toTyPropG typrop kG tyG = tyG_ok !=> typrop_ok
  where
    tyG_ok    = checkClosedTypeG kG tyG
    typrop_ok = typrop (toKind kG) (toClosedType tynames kG tyG)


-- |Stream of names x0, x1, x2, ..
names :: [Text.Text]
names = mkTextNameStream "x"


-- |Stream of type names t0, t1, t2, ..
tynames :: [Text.Text]
tynames = mkTextNameStream "t"

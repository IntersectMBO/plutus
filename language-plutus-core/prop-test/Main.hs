
module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.PropTest
import           Control.Monad.Except

import           Data.Coolean
import           Data.Either

main :: IO ()
main = do
  testTyProp 10 (Type ()) wellKinded
  testTyProp 10 (Type ()) normalizePreservesKind


-- |Property: Generated types are well-kinded.
wellKinded :: TyProp
wellKinded k tyQ = isSafe $ do
  ty <- liftQuote tyQ
  checkKind defOffChainConfig () ty k

-- |Property: Normalisation preserves kind.
normalizePreservesKind :: TyProp
normalizePreservesKind k tyQ = isSafe $ do
  ty <- liftQuote tyQ
  ty' <- unNormalized <$> normalizeTypeFull ty
  checkKind defOffChainConfig () ty' k


-- * Helper functions

-- |Check if the type/kind checker threw any errors.
isSafe :: ExceptT (Error ()) Quote () -> Cool
isSafe = toCool . isRight . runQuote . runExceptT

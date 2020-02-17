
module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.PropTest
import           Language.PlutusCore.Gen.Type
import           Control.Monad.Except
import           Data.Either


main :: IO ()
main = testTy 10 TypeG isWellKinded

-- |Property: Generated types are well-kinded.
isWellKinded :: TyProp
isWellKinded k tyQ = isSafe (liftQuote tyQ >>= \ty -> checkKind defOffChainConfig () ty k)
  where
    isSafe :: ExceptT (TypeError ()) Quote () -> Bool
    isSafe = isRight . runQuote . runExceptT

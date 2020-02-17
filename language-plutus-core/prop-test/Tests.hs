module Tests (tests) where

import           Language.PlutusCore
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.PropTest

import           Control.Monad.Except
import           Distribution.TestSuite
import qualified Data.Coolean as Cool
import           Data.Either
import           Test.Tasty

depth :: Int
depth = 15

kind :: Kind ()
kind = Type ()

tests :: IO [Test]
tests = return [ Test test_wellKinded
               , Test test_normalizePreservesKind
               ]

test_wellKinded :: TestInstance
test_wellKinded = TestInstance
  { run       = testTyProp depth kind prop_wellKinded
  , name      = "WellKinded"
  , tags      = []
  , options   = []
  , setOption = \_ _ -> Right test_wellKinded
  }

test_normalizePreservesKind :: TestInstance
test_normalizePreservesKind = TestInstance
  { run       = testTyProp depth kind prop_normalizePreservesKind
  , name      = "NormalizePreservesKind"
  , tags      = []
  , options   = []
  , setOption = \_ _ -> Right test_normalizePreservesKind
  }

-- |Property: Generated types are well-kinded.
prop_wellKinded :: TyProp
prop_wellKinded k tyQ = isSafe $ do
  ty <- liftQuote tyQ
  checkKind defOffChainConfig () ty k

-- |Property: Normalisation preserves kind.
prop_normalizePreservesKind :: TyProp
prop_normalizePreservesKind k tyQ = isSafe $ do
  ty <- liftQuote tyQ
  ty' <- unNormalized <$> normalizeTypeFull ty
  checkKind defOffChainConfig () ty' k


-- * Helper functions

-- |Check if the type/kind checker threw any errors.
isSafe :: ExceptT (Error ()) Quote () -> Cool.Cool
isSafe = Cool.toCool . isRight . runQuote . runExceptT

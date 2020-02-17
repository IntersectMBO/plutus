import           Language.PlutusCore
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.PropTest

import           Control.Monad.Except
import qualified Data.Coolean as Cool
import           Data.Either
import           Test.Tasty
import           Test.Tasty.HUnit

depth :: Int
depth = 15

kind :: Kind ()
kind = Type ()

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "all tests"
  [ testGroup "types"
    [ testCase "generated types are well-kinded" $ do
        testTyProp depth kind prop_wellKinded
    , testCase "normalization preserves kinds" $ do
        testTyProp depth kind prop_normalizePreservesKind
    ]
  ]


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

module ConstantApplication where

import           Language.PlutusCore
-- TODO: export a single 'Language.PlutusCore.Constant'
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Apply

import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

main :: IO ()
main = defaultMain tests_ConstantApplication

tests_ConstantApplication :: TestTree
tests_ConstantApplication =
    testGroup "constantApplication"
        [ tests_typedBuiltinName
        ]

tests_typedBuiltinName :: TestTree
tests_typedBuiltinName =
    testGroup "typedBuiltinName"
       [ testProperty "typedAddInteger" prop_typedAddInteger
       ]

prop_typedAddInteger :: Property
prop_typedAddInteger = property $ do
    size <- forAll . Gen.integral $ Range.linear 1 4
    let (low, high) = toBoundsInt size
        getInt = forAll . Gen.integral $ Range.linear (low `div` 2) (high `div` 2)
        getBuiltinInt
            = evalEither
            . maybe (Left "prop_typedAddInteger: out of bounds") (Right . Constant ())
            . makeBuiltinInt size
        getIntPair = do
            x <- getInt
            bx <- getBuiltinInt x
            return (x, bx)
    (x, bx) <- getIntPair
    (y, by) <- getIntPair
    let TypedBuiltinName name _ = typedAddInteger
    let rbs = applyBuiltinName name [bx, by]
    s <- getBuiltinInt $ x + y
    rbs === ConstAppSuccess s

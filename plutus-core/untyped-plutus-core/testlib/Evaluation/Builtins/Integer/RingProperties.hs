-- editorconfig-checker-disable
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

-- | Property tests for the `addInteger`, `subtractInteger`, and `multiplyInteger` builtins
module Evaluation.Builtins.Integer.RingProperties (test_integer_ring_properties)
where

import Evaluation.Builtins.Common
import Evaluation.Builtins.Integer.Common

import PlutusCore.Compiler.Erase (eraseTerm)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Version (plcVersion100)
import PlutusPrelude (display)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (CountingSt (..), counting, runCekNoEmit)

import Control.Monad (forM_)
import Data.Char (isAlphaNum)
import Data.IORef (atomicModifyIORef', newIORef)
import Data.Text (Text)
import Data.Text.IO qualified as Text
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((<.>), (</>))
import Text.Printf (printf)

import Test.Tasty (TestName, TestTree, testGroup, withResource)
import Test.Tasty.QuickCheck

type CheckEquality = PlcTerm -> PlcTerm -> Property

{-| Keep the equality assertion and export both expressions as independent
conformance cases. Each property has its own counter, starting at 1 for each
run (including any shrinking attempts). Files from a previous run with the
same names are overwritten; higher-numbered files are left untouched.

Numbers are padded to five digits. Output is relative to the test process's
working directory:
integer-ring-properties/<test-name>-<n>/<test-name>-<n>
with .uplc, .uplc.expected, and .budget.expected extensions. -}
testPropertyWithFiles :: Testable prop => TestName -> (CheckEquality -> prop) -> TestTree
testPropertyWithFiles name prop =
  withResource (newIORef (1 :: Integer)) (const $ pure ()) $ \getCounter ->
    testProperty name $ prop $ \t1 t2 -> ioProperty $ do
      counter <- getCounter
      forM_ [t1, t2] $ \term -> do
        n <- atomicModifyIORef' counter $ \i -> (i + 1, i)
        let caseName = map (\c -> if isAlphaNum c then c else '-') name <> "-" <> printf "%05d" n
            dir = "integer-ring-properties" </> caseName
            path = dir </> caseName <.> "uplc"
            input = eraseTerm term
            (expected, expectedBudget) =
              case runCekNoEmit defaultCekParametersForTesting counting input of
                (Left _, _) -> ("evaluation failure", "evaluation failure")
                (Right result, CountingSt budget) -> (renderProgram result, display budget)
        createDirectoryIfMissing True dir
        Text.writeFile path $ renderProgram input
        Text.writeFile (path <.> "expected") expected
        Text.writeFile (dir </> caseName <.> "budget" <.> "expected") expectedBudget
      pure $ evalOkEq t1 t2
  where
    renderProgram :: UplcTerm -> Text
    renderProgram = display . UPLC.Program () plcVersion100

-- a+(b+c) = (a+b)+c
prop_addition_associative :: CheckEquality -> BigInteger -> BigInteger -> BigInteger -> Property
prop_addition_associative check (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  let t1 = addInteger a (addInteger b c)
      t2 = addInteger (addInteger a b) c
   in check t1 t2

-- a+b = b+a
prop_addition_commutative :: CheckEquality -> BigInteger -> BigInteger -> Property
prop_addition_commutative check (biginteger -> a) (biginteger -> b) =
  check (addInteger a b) (addInteger b a)

-- a+0 = a
prop_zero_additive_identity :: CheckEquality -> BigInteger -> Property
prop_zero_additive_identity check (biginteger -> a) =
  check (addInteger a zero) a

-- (a+b)-b = a
prop_add_subtract_inverse :: CheckEquality -> BigInteger -> BigInteger -> Property
prop_add_subtract_inverse check (biginteger -> a) (biginteger -> b) =
  check (subtractInteger (addInteger a b) b) a

-- a*(b*c) = (a*b)*c
prop_multiplication_associative
  :: CheckEquality -> BigInteger -> BigInteger -> BigInteger -> Property
prop_multiplication_associative check (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  let t1 = multiplyInteger a (multiplyInteger b c)
      t2 = multiplyInteger (multiplyInteger a b) c
   in check t1 t2

-- a*b = b*a
prop_multiplication_commutative :: CheckEquality -> BigInteger -> BigInteger -> Property
prop_multiplication_commutative check (biginteger -> a) (biginteger -> b) =
  let t1 = multiplyInteger a b
      t2 = multiplyInteger b a
   in check t1 t2

-- a*1 = a
prop_one_multiplicative_identity :: CheckEquality -> BigInteger -> Property
prop_one_multiplicative_identity check (biginteger -> a) =
  let t = multiplyInteger a one
   in check t a

-- a*(b+c) = a*b + a*c
prop_distibutive :: CheckEquality -> BigInteger -> BigInteger -> BigInteger -> Property
prop_distibutive check (biginteger -> a) (biginteger -> b) (biginteger -> c) =
  let t1 = multiplyInteger a (addInteger b c)
      t2 = addInteger (multiplyInteger a b) (multiplyInteger a c)
   in check t1 t2

test_integer_ring_properties :: TestTree
test_integer_ring_properties =
  testGroup
    "Ring properties for integer arithmetic builtins"
    [ testPropertyWithFiles "addInteger is associative" prop_addition_associative
    , testPropertyWithFiles "addInteger is commutative" prop_addition_commutative
    , testPropertyWithFiles "0 is an identity element for addInteger" prop_zero_additive_identity
    , testPropertyWithFiles "subtraction is the inverse of addition" prop_add_subtract_inverse
    , testPropertyWithFiles "multiplyInteger is associative" prop_multiplication_associative
    , testPropertyWithFiles "multiplyInteger is commutative" prop_multiplication_commutative
    , testPropertyWithFiles "1 is a multiplicative identity" prop_one_multiplicative_identity
    , testPropertyWithFiles "multiplyInteger distributes over addInteger" prop_distibutive
    ]

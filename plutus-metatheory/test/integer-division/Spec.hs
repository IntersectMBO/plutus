{-| Differential property tests of the Agda implementations of the integer
   division builtins against Haskell's @quot@\/@rem@\/@div@\/@mod@.

   The functions under test are the MAlonzo-compiled partial denotations
   exported from @Builtin.Integer.Base@ under stable names via @COMPILE GHC@
   pragmas.  @Builtin.Integer.Properties@ proves (in Agda) that these
   denotations apply the genuine @quot@\/@rem@\/@div@\/@mod@ on every non-zero
   divisor and fail exactly on zero, so these properties transitively test the
   real implementations — the ones the CEK machine executes via
   @Builtin.CInteger@. -}
module Main (main) where

import Evaluation.Builtins.Integer.Common (BigInteger (..))
import MAlonzo.Code.Builtin.Integer.Base
  ( agdaDivideInteger
  , agdaModInteger
  , agdaQuotientInteger
  , agdaRemainderInteger
  )

import Test.Tasty
import Test.Tasty.QuickCheck

numberOfTests :: Int
numberOfTests = 1000

testProp :: Testable prop => TestName -> prop -> TestTree
testProp s p = testProperty s $ withNumTests numberOfTests p

{-| Haskell's reference semantics for a division builtin: fail on a zero
divisor, otherwise apply the operator. -}
haskellSemantics :: (Integer -> Integer -> Integer) -> Integer -> Integer -> Maybe Integer
haskellSemantics op n d = if d == 0 then Nothing else Just (n `op` d)

agreesWith
  :: TestName
  -> (Integer -> Integer -> Maybe Integer)
  -> (Integer -> Integer -> Integer)
  -> TestTree
agreesWith name agdaF hsF =
  testGroup
    name
    [ testProp "agrees with Haskell" $
        \(BigInteger a) (BigInteger b) ->
          agdaF a b === haskellSemantics hsF a b
    , testProp "fails on a zero divisor" $
        \(BigInteger a) -> agdaF a 0 === Nothing
    ]

tests :: TestTree
tests =
  testGroup
    "Compiled Agda integer division vs Haskell"
    [ agreesWith "quotientInteger vs quot" agdaQuotientInteger quot
    , agreesWith "remainderInteger vs rem" agdaRemainderInteger rem
    , agreesWith "divideInteger vs div" agdaDivideInteger div
    , agreesWith "modInteger vs mod" agdaModInteger mod
    , testProp "divideInteger and modInteger pair up like divMod" $
        \(BigInteger a) (BigInteger b) ->
          b
            /= 0
            ==> let (q, r) = a `divMod` b
                 in (agdaDivideInteger a b, agdaModInteger a b) === (Just q, Just r)
    ]

main :: IO ()
main = defaultMain tests

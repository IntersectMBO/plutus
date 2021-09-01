{-# LANGUAGE LambdaCase  #-}
{-# LANGUAGE QuasiQuotes #-}

module Suites.Natural (tests) where

import           PlutusTx.Arbitrary         ()
import           PlutusTx.Builtins.Internal
import           PlutusTx.Natural
import           PlutusTx.Numeric.Class
import qualified PlutusTx.Prelude           as Plutus
import           Prelude                    hiding (divMod, product, rem)
import           Test.QuickCheck            (Property, forAllShrink, (.&&.), (.||.), (=/=), (===))
import           Test.QuickCheck.Arbitrary  (arbitrary, shrink)
import           Test.Tasty                 (TestTree, localOption, testGroup)
import           Test.Tasty.QuickCheck      (QuickCheckTests, testProperty)

tests :: [TestTree]
tests =
  [ localOption go . testGroup "EuclideanClosed" $
      [ testProperty "if divMod x y = (d, r), then (d * y) + r = x" ecProp1
      , testProperty "divMod x 0 = (0, x)" ecProp2
      , testProperty "if divMod x y = (d, r) and y /= 0, then 0 <= |r| < |y|" ecProp3
      ]
  , localOption go . testGroup "Monus" $
      [ testProperty "a + (b ^- a) = b + (a ^- b)" monusProp1
      , testProperty "(a ^- b) ^- c = a ^- (b + c)" monusProp2
      , testProperty "a ^- a = 0" monusProp3
      , testProperty "0 ^- a = 0" monusProp4
      ]
  , localOption go . testProperty "Parity" $ parityProp
  , localOption go . testGroup "Exponentiation" $
      [ testProperty "x ^+ 0 = mempty" expProp1
      , testProperty "x ^+ 1 = x" expProp2
      , testProperty "x ^+ n = fold . repeat n $ x" expProp3
      ]
  ]
  where
    go :: QuickCheckTests
    go = 1000000

expProp1 :: Property
expProp1 = forAllShrink arbitrary shrink go
  where
    go :: Natural -> Property
    go x = x ^+ Plutus.zero === Plutus.one

expProp2 :: Property
expProp2 = forAllShrink arbitrary shrink go
  where
    go :: Natural -> Property
    go x = x ^+ Plutus.one === x

expProp3 :: Property
expProp3 = forAllShrink arbitrary shrink go
  where
    go :: (Natural, Natural) -> Property
    go (x, n) = x ^+ n === (product . clone n $ x)
    clone :: Natural -> Natural -> [Natural]
    clone n x =
      if n == Plutus.zero
        then []
        else x : clone (n ^- Plutus.one) x
    product :: [Natural] -> Natural
    product = \case
      []       -> Plutus.one
      (n : ns) -> n Plutus.* product ns

ecProp1 :: Property
ecProp1 = forAllShrink arbitrary shrink go
  where
    go :: (Natural, Natural) -> Property
    go (x, y) =
      let BuiltinPair (d, r) = divMod x y
       in (d Plutus.* y) Plutus.+ r === x

ecProp2 :: Property
ecProp2 = forAllShrink arbitrary shrink go
  where
    go :: Natural -> Property
    go x = divMod x Plutus.zero === BuiltinPair (Plutus.zero, x)

ecProp3 :: Property
ecProp3 = forAllShrink arbitrary shrink go
  where
    go :: (Natural, Natural) -> Property
    go (x, y) =
      let BuiltinPair (_, r) = divMod x y
       in (y === Plutus.zero)
            .||. ( (Plutus.compare Plutus.zero r =/= GT)
                    .&&. (Plutus.compare r y === LT)
                 )

monusProp1 :: Property
monusProp1 = forAllShrink arbitrary shrink go
  where
    go :: (Natural, Natural) -> Property
    go (x, y) = (x Plutus.+ (y ^- x)) === (y Plutus.+ (x ^- y))

monusProp2 :: Property
monusProp2 = forAllShrink arbitrary shrink go
  where
    go :: (Natural, Natural, Natural) -> Property
    go (x, y, z) = ((x ^- y) ^- z) === (x ^- (y Plutus.+ z))

monusProp3 :: Property
monusProp3 = forAllShrink arbitrary shrink go
  where
    go :: Natural -> Property
    go x = x ^- x === Plutus.zero

monusProp4 :: Property
monusProp4 = forAllShrink arbitrary shrink go
  where
    go :: Natural -> Property
    go x = Plutus.zero ^- x === Plutus.zero

parityProp :: Property
parityProp = forAllShrink arbitrary shrink go
  where
    go :: Natural -> Property
    go x = case x `rem` [nat| 2 |] of
      [nat| 0 |] -> parity x === Even
      _          -> parity x === Odd

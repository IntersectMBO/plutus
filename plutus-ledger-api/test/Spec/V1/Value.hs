{-# LANGUAGE MultiWayIf #-}

module Spec.V1.Value where

import PlutusLedgerApi.Test.V1.Value as Value
import PlutusLedgerApi.V1
import PlutusLedgerApi.V1.Value
import PlutusTx.Numeric qualified as Numeric

import Control.Lens
import Test.Tasty
import Test.Tasty.QuickCheck

infix 4 <=>, </>

-- | Ensure that @x@ equals @y@ and vice versa. The latter part is needed to ensure that @(==)@ is
-- symmetric for the specific type.
(<=>) :: (Eq a, Show a) => a -> a -> Property
x <=> y = x === y .&&. y === x

-- | Ensure that @x@ doesn't equal @y@ and vice versa. The latter part is needed to ensure that
-- @(/=)@ is symmetric for the specific type.
(</>) :: (Eq a, Show a) => a -> a -> Property
x </> y = x =/= y .&&. y =/= x

scaleTestsBy :: Testable prop => Int -> prop -> Property
scaleTestsBy factor = withMaxSuccess (100 * factor) . mapSize (* factor)

-- | Apply a function to an arbitrary number of elements of the given list. The elements are chosen
-- at random.
mapMany :: (a -> Gen a) -> [a] -> Gen [a]
mapMany f = traverse $ \x -> do
    b <- arbitrary
    if b then f x else pure x

-- | Apply a function to an arbitrary non-zero number of elements of the given list. The elements
-- are chosen at random.
mapSome :: Eq a => (a -> Gen a) -> [a] -> Gen [a]
mapSome f xs = do
    i <- choose (0, length xs - 1)
    xs' <- mapMany f xs
    let xi = xs !! i
    ix i (\x -> if x == xi then f x else pure x) xs'

-- | Generate an 'Integer' that is not equal to the given one.
updateInteger :: Integer -> Gen Integer
updateInteger i = arbitrary `suchThat` (/= i)

onLists
    :: Value
    -> ([(CurrencySymbol, [(TokenName, Integer)])] ->
        Gen [(CurrencySymbol, [(TokenName, Integer)])])
    -> (Value -> Property)
    -> Property
onLists value f = forAll (fmap listsToValue . f $ valueToLists value)

-- | Test that the 'Monoid' instance of 'Value' is law-abiding and that merging two non-zero values
-- creates a value that isn't equal to any of the original ones.
test_Monoid :: TestTree
test_Monoid = testProperty "Monoid" . scaleTestsBy 5 $ \value1 ->
    if isZero value1
        then conjoin
            [ value1 <=> mempty
            , forAll arbitrary $ \value2 -> value1 <> value2 <=> value2
            ]
        else conjoin
            [ value1 </> mempty
            , value1 <> value1 <=> Numeric.scale 2 value1
            , forAll arbitrary $ \value2 ->
                if isZero value2
                    then value1 <> value2 <=> value1
                    else conjoin
                        [ value1 <> value2 </> value1
                        , value1 <> value2 </> value2
                        , value1 <> value2 <=> value2 <> value1
                        , forAll arbitrary $ \value3 ->
                            not (isZero value3) ==>
                                (value1 <> value2) <> value3 <=> value1 <> (value2 <> value3)
                        ]
            ]

-- | Test that changing the values of some of the 'TokenName's creates a different 'Value'.
test_updateSome :: TestTree
test_updateSome = testProperty "updateSome" . scaleTestsBy 10 $ \value ->
    let lists = valueToLists value
    in not (null lists || any (any null) lists) ==>
        onLists value (mapSome . traverse . mapSome $ traverse updateInteger)
            (\value' -> value </> value')

-- | Test that shuffling 'CurrencySymbol's or 'TokenName's creates a 'Value' that is equal to the
-- original one.
test_shuffle :: TestTree
test_shuffle = testProperty "shuffle" . scaleTestsBy 10 $ \value1 ->
    conjoin
        [ onLists value1 shuffle $ \value1' -> value1 <=> value1'
        , onLists value1 (mapMany $ traverse shuffle) $ \value1' -> value1 <=> value1'
        ]

test_split :: TestTree
test_split = testProperty "split" . scaleTestsBy 7 $ \value ->
    let (valueL, valueR) = split value
    in Numeric.negate valueL <> valueR <=> value

test_Value :: TestTree
test_Value = testGroup "Value"
    [ test_Monoid
    , test_updateSome
    , test_shuffle
    , test_split
    ]

{-# LANGUAGE MultiWayIf #-}

module Spec.V1.Value where

import PlutusLedgerApi.Test.V1.Value as Value
import PlutusLedgerApi.V1
import PlutusLedgerApi.V1.Value
import PlutusTx.Numeric qualified as Numeric

import Control.Lens
import Test.Tasty
import Test.Tasty.QuickCheck

infix 4 <=>
(<=>) :: (Eq a, Show a) => a -> a -> Property
x <=> y = x === y .&&. y === x

infix 4 </>
(</>) :: (Eq a, Show a) => a -> a -> Property
x </> y = x =/= y .&&. y =/= x

scaleTestsBy :: Testable prop => Int -> prop -> Property
scaleTestsBy factor = withMaxSuccess (100 * factor) . mapSize (* factor)

mapMany :: (a -> Gen a) -> [a] -> Gen [a]
mapMany f = traverse $ \x -> do
    b <- arbitrary
    if b then f x else pure x

mapSome :: Eq a => (a -> Gen a) -> [a] -> Gen [a]
mapSome f xs = do
    i <- choose (0, length xs - 1)
    xs' <- mapMany f xs
    let xi = xs !! i
    ix i (\x -> if x == xi then f x else pure x) xs'

updateInteger :: Integer -> Gen Integer
updateInteger i = arbitrary `suchThat` (/= i)

onLists
    :: Value
    -> ([(CurrencySymbol, [(TokenName, Integer)])] ->
        Gen [(CurrencySymbol, [(TokenName, Integer)])])
    -> (Value -> Property)
    -> Property
onLists value f = forAll (fmap listsToValue . f $ valueToLists value)

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

test_updateSome :: TestTree
test_updateSome = testProperty "updateSome" . scaleTestsBy 15 $ \value ->
    any (any $ not . null) (valueToLists value) ==>
        onLists value (mapSome . traverse . mapSome $ traverse updateInteger)
            (\value' -> value =/= value')

test_unordered :: TestTree
test_unordered = testProperty "unordered" . scaleTestsBy 10 $ \value1 ->
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
    , test_unordered
    , test_split
    ]

module Spec.V1.Data.Value where

import PlutusLedgerApi.Test.V1.Data.Value as Value

-- TODO: import a new PlutusLedgerApi.Data.V1 module instead
import PlutusLedgerApi.V1.Data.Value
import PlutusTx.Numeric qualified as Numeric

import Control.Lens
import Data.List (sort)
import Test.Tasty
import Test.Tasty.QuickCheck

infix 4 <=>, </>

{-| Ensure that @x@ equals @y@ and vice versa. The latter part is needed to ensure that @(==)@ is
symmetric for the specific type. -}
(<=>) :: (Eq a, Show a) => a -> a -> Property
x <=> y = x === y .&&. y === x

{-| Ensure that @x@ doesn't equal @y@ and vice versa. The latter part is needed to ensure that
@(/=)@ is symmetric for the specific type. -}
(</>) :: (Eq a, Show a) => a -> a -> Property
x </> y = x =/= y .&&. y =/= x

scaleTestsBy :: Testable prop => Int -> prop -> Property
scaleTestsBy factor = withMaxSuccess (100 * factor) . mapSize (* factor)

{-| Apply a function to an arbitrary number of elements of the given list. The elements are chosen
at random. -}
mapMany :: (a -> Gen a) -> [a] -> Gen [a]
mapMany f = traverse $ \x -> do
  b <- arbitrary
  if b then f x else pure x

{-| Apply a function to an arbitrary non-zero number of elements of the given list. The elements
are chosen at random. -}
mapSome :: Eq a => (a -> Gen a) -> [a] -> Gen [a]
mapSome f xs = do
  xs' <- mapMany f xs
  i <- choose (0, length xs - 1)
  let xi = xs !! i
  ix i (\x -> if x == xi then f x else pure x) xs'

-- | Generate an 'Integer' that is not equal to the given one.
updateInteger :: Integer -> Gen Integer
updateInteger i = arbitrary `suchThat` (/= i)

{-| Generate new 'TokenName's such that the resulting list, being sorted, is not equal to the given
one, being sorted as well. -}
freshenTokenNames :: [(TokenName, Integer)] -> Gen [(TokenName, Integer)]
freshenTokenNames tokens =
  uniqueNames TokenName (map snd tokens) `suchThat` \tokens' ->
    sort (filter ((/= 0) . snd) tokens) /= sort (filter ((/= 0) . snd) tokens')

onLists
  :: Value
  -> ( [(CurrencySymbol, [(TokenName, Integer)])]
       -> Gen [(CurrencySymbol, [(TokenName, Integer)])]
     )
  -> (Value -> Property)
  -> Property
onLists value f = forAll (fmap listsToValue . f $ valueToLists value)

-- | Test various laws for operations over 'Value'.
test_laws :: TestTree
test_laws = testProperty "laws" . scaleTestsBy 5 $ \value1 ->
  conjoin
    [ value1 <> value1 <=> Numeric.scale 2 value1
    , value1 <> Numeric.negate value1 <=> mempty
    , if isZero value1
        then
          conjoin
            [ value1 <=> mempty
            , forAll arbitrary $ \value2 -> value1 <> value2 <=> value2
            ]
        else
          conjoin
            [ value1 </> mempty
            , forAll arbitrary $ \value2 ->
                if isZero value2
                  then value1 <> value2 <=> value1
                  else
                    conjoin
                      [ value1 <> value2 </> value1
                      , value1 <> value2 </> value2
                      , value1 <> value2 <=> value2 <> value1
                      , forAll arbitrary $ \value3 ->
                          not (isZero value3) ==>
                            (value1 <> value2) <> value3 <=> value1 <> (value2 <> value3)
                      ]
            ]
    ]

{-| Test that changing the values of some of the values of 'TokenName's creates a different
'Value'. -}
test_updateSomeTokenValues :: TestTree
test_updateSomeTokenValues = testProperty "updateSomeTokenValues" . scaleTestsBy 15 $ \prevalue ->
  let lists = filter (not . null . snd) $ valueToLists prevalue
      value = listsToValue lists
   in not (null lists) ==>
        onLists
          value
          (mapSome . traverse . mapSome $ traverse updateInteger)
          (\value' -> value </> value')

-- | Test that changing the values of some of the 'TokenName's creates a different 'Value'.
test_updateSomeTokenNames :: TestTree
test_updateSomeTokenNames = testProperty "updateSomeTokenNames" . scaleTestsBy 15 $ \prevalue ->
  let lists =
        filter (not . null . snd) . map (fmap . filter $ (/= 0) . snd) $
          valueToLists prevalue
      value = listsToValue lists
   in not (null lists) ==>
        onLists
          value
          (mapSome $ traverse freshenTokenNames)
          (\value' -> value </> value')

{-| Test that shuffling 'CurrencySymbol's or 'TokenName's creates a 'Value' that is equal to the
original one. -}
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
test_Value =
  testGroup
    "Value"
    [ test_laws
    , test_updateSomeTokenValues
    , test_updateSomeTokenNames
    , test_shuffle
    , test_split
    ]

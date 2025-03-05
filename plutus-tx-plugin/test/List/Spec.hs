module List.Spec where

import Test.Tasty (TestTree, localOption, testGroup)
import Test.Tasty.Hedgehog (HedgehogTestLimit (..), testProperty)

import List.Properties1
import List.Properties2
import List.Semantics

propertyTests :: TestTree
propertyTests =
  localOption (HedgehogTestLimit (Just 30))
  $ testGroup "List property tests"
    [ testProperty "areInverses" areInversesSpec
    , testProperty "toSOP" toSOPSpec
    , testProperty "fromSOP" fromSOPSpec
    , testProperty "append" appendSpec
    , testProperty "find" findSpec
    , testProperty "findIndices" findIndicesSpec
    , testProperty "filter" filterSpec
    , testProperty "mapMaybe" mapMaybeSpec
    , testProperty "any" anySpec
    , testProperty "all" allSpec
    , testProperty "foldMap" foldMapSpec
    , testProperty "map" mapSpec
    , testProperty "length" lengthSpec
    , testProperty "uncons" unconsSpec
    , testProperty "and" andSpec
    , testProperty "or" orSpec
    , testProperty "elem" elemSpec
    , testProperty "notElem" notElemSpec
    , testProperty "foldr" foldrSpec
    , testProperty "foldl" foldlSpec
    , testProperty "concat" concatSpec
    , testProperty "concatMap" concatMapSpec
    , testProperty "listToMaybe" listToMaybeSpec
    , testProperty "uniqueElement" uniqueElementSpec
    , testProperty "index" indexSpec
    , testProperty "revAppend" revAppendSpec
    , testProperty "reverse" reverseSpec
    , testProperty "findIndex" findIndexSpec
    , testProperty "unzip" unzipSpec
    , testProperty "zipWith" zipWithSpec
    , testProperty "head" headSpec
    , testProperty "last" lastSpec
    , testProperty "tail" tailSpec
    , testProperty "take" takeSpec
    , testProperty "drop" dropSpec
    , testProperty "dropWhile" dropWhileSpec
    , testProperty "splitAt" splitAtSpec
    , testProperty "elemBy" elemBySpec
    , testProperty "nubBy" nubBySpec
    , testProperty "nub" nubSpec
    , testProperty "partition" partitionSpec
    , testProperty "replicate" replicateSpec
    ]

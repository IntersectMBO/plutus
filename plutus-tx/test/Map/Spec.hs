{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
module Map.Spec (tests) where

import Control.Applicative
import Data.List qualified as L
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Property qualified as Prop
import Hedgehog.Range qualified as Range
import PlutusTx.Map hiding (empty, foldr)
import PlutusTx.Map qualified as Map
import PlutusTx.Prelude qualified as P
import Prelude hiding (lookup, map)
import Test.Tasty
import Test.Tasty.Hedgehog

genMap :: (P.Ord k) => Gen k -> Gen v -> Gen (Map k v)
genMap genKey genValue = Gen.recursive
    Gen.choice
    [pure Map.empty]
    [insert <$> genKey <*> genValue <*> genMap genKey genValue]

genIntKey :: Gen Integer
genIntKey = Gen.integral (Range.linear 0 100)

genIntValue :: Gen Integer
genIntValue = Gen.integral (Range.linear 0 100)

genIntMap :: Gen (Map Integer Integer)
genIntMap = genMap genIntKey genIntValue

prop_GenValid :: Property
prop_GenValid = property $ do
    t <- forAll genIntMap
    assert (valid t)

prop_NilValid :: Property
prop_NilValid = property $ assert (valid (Map.empty @Integer @Integer))

prop_InsertValid :: Property
prop_InsertValid = property $ do
    k <- forAll genIntKey
    v <- forAll genIntValue
    t <- forAll genIntMap
    assert $ valid (insert k v t)

{-
prop_DeleteValid :: Property
prop_DeleteValid = property $ do
    k <- forAll genIntKey
    t <- forAll genIntMap
    assert $ valid compare (delete compare k t)
-}

prop_UnionValid :: Property
prop_UnionValid = property $ do
    t1 <- forAll genIntMap
    t2 <- forAll genIntMap
    let u = union t1 t2
    annotateShow $ u
    assert $ valid u

prop_NilPost :: Property
prop_NilPost = property $ do
    k <- forAll genIntKey
    lookup k (Map.empty @Integer @Integer) === Nothing

prop_InsertPost :: Property
prop_InsertPost = property $ do
  k <- forAll genIntKey
  k' <- forAll genIntKey
  v <- forAll genIntValue
  t <- forAll genIntMap
  lookup k' (insert k v t) === if k==k' then Just v else lookup k' t

{-
prop_DeletePost :: Property
prop_DeletePost = property $ do
  k <- forAll genIntKey
  k' <- forAll genIntKey
  t <- forAll genIntMap
  lookup compare k' (delete compare k t) === if k==k' then Nothing else lookup compare k' t
-}

prop_LookupPostPresent :: Property
prop_LookupPostPresent = property $ do
  k <- forAll genIntKey
  v <- forAll genIntValue
  t <- forAll genIntMap
  lookup k (insert k v t) === Just v

{-
prop_LookupPostAbsent :: Property
prop_LookupPostAbsent = property $ do
  k <- forAll genIntKey
  t <- forAll genIntMap
  lookup compare k (delete compare k t) === Nothing
-}

prop_UnionPost :: Property
prop_UnionPost = property $ do
  k <- forAll genIntKey
  t1 <- forAll genIntMap
  t2 <- forAll genIntMap
  lookup k (union t1 t2) === (lookup k t1 <|> lookup k t2)

prop_UnionListPost :: Property
prop_UnionListPost = property $ do
  k <- forAll genIntKey
  ts <- forAll (Gen.list (Range.linear 0 1000) genIntMap)
  lookup k (foldr (\m1 m2 -> union m1 m2) Map.empty ts)
    === foldr (\m res -> lookup k m <|> res) empty ts

prop_SizeNil :: Property
prop_SizeNil = property $ size (Map.empty @Integer @Integer) === 0

prop_SizeInsert :: Property
prop_SizeInsert = property $ do
  k <- forAll genIntKey
  v <- forAll genIntValue
  t <- forAll genIntMap
  assert $ size (insert k v t) >= size t

{-
prop_SizeDelete :: Property
prop_SizeDelete = property $ do
  k <- forAll genIntKey
  t <- forAll genIntMap
  assert $ size (delete compare k t) <= size t
-}

prop_SizeUnion :: Property
prop_SizeUnion = property $ do
  t1 <- forAll genIntMap
  t2 <- forAll genIntMap
  assert $ size (union t1 t2) <= size t1 + size t2

deleteKey :: Eq k => k -> [(k, v)] -> [(k, v)]
deleteKey k = filter ((/=k).fst)

prop_NilModel :: Property
prop_NilModel = property $ toList (Map.empty @Integer @Integer) === []

prop_InsertModel :: Property
prop_InsertModel = property $ do
  k <- forAll genIntKey
  v <- forAll genIntValue
  t <- forAll genIntMap
  toList (insert k v t) === L.insert (k,v) (deleteKey k $ toList t)

{-
prop_DeleteModel :: Property
prop_DeleteModel = property $ do
  k <- forAll genIntKey
  t <- forAll genIntMap
  toList (delete compare k t) === deleteKey k (toList t)
-}

prop_LookupModel :: Property
prop_LookupModel = property $ do
  k <- forAll genIntKey
  t <- forAll genIntMap
  lookup k t === L.lookup k (toList t)

prop_UnionModel :: Property
prop_UnionModel = property $ do
  t1 <- forAll genIntMap
  t2 <- forAll genIntMap
  toList (union t1 t2) === L.sort (toList t1 ++ foldr deleteKey (toList t2) (keys t1))

tests :: TestTree
tests =
    let g = $$(discover)
    -- TODO: upstream this
    in testGroup
       (Prop.unGroupName $ groupName g)
       (fmap (\(n, p) -> testProperty (Prop.unPropertyName n) p) (groupProperties g))

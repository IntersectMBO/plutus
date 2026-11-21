{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Universe.Spec (tests) where

import PlutusCore.Default
import PlutusPrelude

import Test.Tasty
import Test.Tasty.HUnit

-- These tags have distinct shapes, including higher-kinded and partially applied constructors.
tags :: [SomeTypeIn DefaultUni]
tags =
  [ SomeTypeIn DefaultUniInteger
  , SomeTypeIn DefaultUniByteString
  , SomeTypeIn DefaultUniString
  , SomeTypeIn DefaultUniUnit
  , SomeTypeIn DefaultUniBool
  , SomeTypeIn DefaultUniProtoList
  , SomeTypeIn DefaultUniProtoArray
  , SomeTypeIn DefaultUniProtoPair
  , SomeTypeIn DefaultUniData
  , SomeTypeIn DefaultUniBLS12_381_G1_Element
  , SomeTypeIn DefaultUniBLS12_381_G2_Element
  , SomeTypeIn DefaultUniBLS12_381_MlResult
  , SomeTypeIn DefaultUniValue
  , SomeTypeIn (DefaultUniList DefaultUniInteger)
  , SomeTypeIn (DefaultUniList DefaultUniBool)
  , SomeTypeIn (DefaultUniList (DefaultUniList DefaultUniInteger))
  , SomeTypeIn (DefaultUniList (DefaultUniList DefaultUniBool))
  , SomeTypeIn (DefaultUniArray DefaultUniInteger)
  , SomeTypeIn (DefaultUniArray DefaultUniBool)
  , SomeTypeIn (DefaultUniApply DefaultUniProtoPair DefaultUniInteger)
  , SomeTypeIn (DefaultUniApply DefaultUniProtoPair DefaultUniBool)
  , SomeTypeIn (DefaultUniPair DefaultUniInteger DefaultUniBool)
  , SomeTypeIn (DefaultUniPair DefaultUniBool DefaultUniInteger)
  , SomeTypeIn (DefaultUniPair DefaultUniInteger DefaultUniInteger)
  , SomeTypeIn (DefaultUniList (DefaultUniPair DefaultUniInteger DefaultUniBool))
  ]

matchesCached :: forall a. DefaultUni a -> [SomeTypeIn DefaultUni] -> [Bool]
matchesCached expected =
  let check :: forall b. DefaultUni b -> Maybe (a :~: b)
      check = geq expected
      {-# NOINLINE check #-}
   in map (\(SomeTypeIn actual) -> isJust (check actual))

tests :: TestTree
tests =
  testGroup
    "universe equality"
    [ testCase "saturated comparisons distinguish all representative tags" $
        for_ (zip [0 :: Int ..] tags) $ \(i, SomeTypeIn expected) ->
          for_ (zip [0 :: Int ..] tags) $ \(j, SomeTypeIn actual) ->
            isJust (geq expected actual) @?= (i == j)
    , testCase "a cached checker distinguishes all representative tags" $
        for_ (zip [0 :: Int ..] tags) $ \(i, SomeTypeIn expected) -> do
          let indices = [0 .. length tags - 1]
          matchesCached expected (tags ++ reverse tags)
            @?= map (i ==) (indices ++ reverse indices)
    ]

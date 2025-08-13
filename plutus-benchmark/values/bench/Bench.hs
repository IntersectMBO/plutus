{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import PlutusBenchmark.Common (getConfig)
import PlutusBenchmark.Values.FlattenedValue qualified as FlattenedValue
import PlutusBenchmark.Values.MMValue qualified as MMValue
import PlutusBenchmark.Values.MockValues
import PlutusBenchmark.Values.NestedValue qualified as NestedValue

import Criterion.Main (bench, bgroup, defaultMainWith, env, nf)

setupEnvNested1 :: IO NestedValue.Value
setupEnvNested1 =
    let (nValue, _, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
     in pure nValue

setupEnvNested2 :: IO (NestedValue.Value, NestedValue.Value)
setupEnvNested2 =
    let (nValue1, _, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (nValue2, _, _) =
            mkMockValues
                mockNumPolicies2
                mockNumTokensPerPolicy2
                mockTokenValues2
     in pure (nValue1, nValue2)

setupEnvFlattened1 :: IO FlattenedValue.Value
setupEnvFlattened1 =
    let (_, fValue, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
     in pure fValue

setupEnvFlattened2 :: IO (FlattenedValue.Value, FlattenedValue.Value)
setupEnvFlattened2 =
    let (_, fValue1, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (_, fValue2, _) =
            mkMockValues
                mockNumPolicies2
                mockNumTokensPerPolicy2
                mockTokenValues2
     in pure (fValue1, fValue2)

setupEnvMM1 :: IO MMValue.Value
setupEnvMM1 =
    let (_, _, mmValue) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
     in pure mmValue

setupEnvMM2 :: IO (MMValue.Value, MMValue.Value)
setupEnvMM2 =
    let (_, _, mmValue1) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (_, _, mmValue2) =
            mkMockValues
                mockNumPolicies2
                mockNumTokensPerPolicy2
                mockTokenValues2
     in pure (mmValue1, mmValue2)

setupEnvNested1andInv :: IO (NestedValue.Value, NestedValue.Value)
setupEnvNested1andInv =
    let (nValue1, _, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (nValue1Inv, _, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                (map negate mockTokenValues1)
     in pure (nValue1, nValue1Inv)

setupEnvFlattened1andInv :: IO (FlattenedValue.Value, FlattenedValue.Value)
setupEnvFlattened1andInv =
    let (_, fValue1, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (_, fValue1Inv, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                (map negate mockTokenValues1)
     in pure (fValue1, fValue1Inv)

setupEnvMM1andInv :: IO (MMValue.Value, MMValue.Value)
setupEnvMM1andInv =
    let (_, _, mmValue1) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (_, _, mmValue1Inv) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                (map negate mockTokenValues1)
     in pure (mmValue1, mmValue1Inv)

main :: IO ()
main = do
    config <- getConfig 30
    defaultMainWith config $
        [ env setupEnvNested1 $ \ ~nValue ->
            bgroup "NestedValue"
                [ bench "insertCoin - new coin"
                    $ nf (NestedValue.insertCoin polId500 tokN10000 200) nValue
                , bench "insertCoin - existing coin"
                    $ nf (NestedValue.insertCoin polId500 tokN999999 200) nValue
                , bench "lookupCoin - not found"
                    $ nf (NestedValue.lookupCoin polId500 tokN10000) nValue
                , bench "lookupCoin - existing coin"
                    $ nf (NestedValue.lookupCoin polId500 tokN999999) nValue
                , bench "deleteCoin - not found"
                    $ nf (NestedValue.deleteCoin polId500 tokN10000) nValue
                , bench "deleteCoin - existing coin"
                    $ nf (NestedValue.deleteCoin polId500 tokN999999) nValue
                , bench "byPolicyId - not found"
                    $ nf (NestedValue.byPolicyId polIdNotHere) nValue
                , bench "byPolicyId - existing policy"
                    $ nf (NestedValue.byPolicyId polId500) nValue
                , bench "byTokenName - not found"
                    $ nf (NestedValue.byTokenName polIdNotHere) nValue
                , bench "byTokenName - existing token"
                    $ nf (NestedValue.byTokenName tokN999999) nValue
                ]
        , env setupEnvFlattened1 $ \ ~fValue ->
            bgroup "FlattenedValue"
                [ bench "insertCoin - new coin"
                    $ nf (FlattenedValue.insertCoin polId500 tokN10000 200) fValue
                , bench "insertCoin - existing coin"
                    $ nf (FlattenedValue.insertCoin polId500 tokN999999 200) fValue
                , bench "lookupCoin - not found"
                    $ nf (FlattenedValue.lookupCoin polId500 tokN10000) fValue
                , bench "lookupCoin - existing coin"
                    $ nf (FlattenedValue.lookupCoin polId500 tokN999999) fValue
                , bench "deleteCoin - not found"
                    $ nf (FlattenedValue.deleteCoin polId500 tokN10000) fValue
                , bench "deleteCoin - existing coin"
                    $ nf (FlattenedValue.deleteCoin polId500 tokN999999) fValue
                , bench "byPolicyId - not found"
                    $ nf (FlattenedValue.byPolicyId polIdNotHere) fValue
                , bench "byPolicyId - existing policy"
                    $ nf (FlattenedValue.byPolicyId polId500) fValue
                , bench "byTokenName - not found"
                    $ nf (FlattenedValue.byTokenName polIdNotHere) fValue
                , bench "byTokenName - existing token"
                    $ nf (FlattenedValue.byTokenName tokN999999) fValue
                ]
        , env setupEnvMM1 $ \ ~mmValue ->
            bgroup "MMValue"
                [ bench "insertCoin - new coin"
                    $ nf (MMValue.insertCoin polId500 tokN10000 200) mmValue
                , bench "insertCoin - existing coin"
                    $ nf (MMValue.insertCoin polId500 tokN999999 200) mmValue
                , bench "lookupCoin - not found"
                    $ nf (MMValue.lookupCoin polId500 tokN10000) mmValue
                , bench "lookupCoin - existing coin"
                    $ nf (MMValue.lookupCoin polId500 tokN999999) mmValue
                , bench "deleteCoin - not found"
                    $ nf (MMValue.deleteCoin polId500 tokN10000) mmValue
                , bench "deleteCoin - existing coin"
                    $ nf (MMValue.deleteCoin polId500 tokN999999) mmValue
                , bench "byPolicyId - not found"
                    $ nf (MMValue.byPolicyId polIdNotHere) mmValue
                , bench "byPolicyId - existing policy"
                    $ nf (MMValue.byPolicyId polId500) mmValue
                , bench "byTokenName - not found"
                    $ nf (MMValue.byTokenName polIdNotHere) mmValue
                , bench "byTokenName - existing token"
                    $ nf (MMValue.byTokenName tokN999999) mmValue
                ]
        , env setupEnvNested2 $ \ ~vals ->
            bgroup "NestedValue"
                [ bench "union - two different values"
                    $ nf (uncurry NestedValue.union) vals
                , bench "valueContains - is not sub-value"
                    $ nf (uncurry NestedValue.valueContains) vals
                ]
        , env setupEnvFlattened2 $ \ ~vals ->
            bgroup "FlattenedValue"
                [ bench "union - two different values"
                    $ nf (uncurry FlattenedValue.union) vals
                , bench "valueContains - is not sub-value"
                    $ nf (uncurry FlattenedValue.valueContains) vals
                ]
        , env setupEnvMM2 $ \ ~vals ->
            bgroup "MMValue"
                [ bench "union - two different values"
                    $ nf (uncurry MMValue.union) vals
                , bench "valueContains - is not sub-value"
                    $ nf (uncurry MMValue.valueContains) vals
                ]
        , env setupEnvNested1andInv $ \ ~vals ->
            bgroup "NestedValue"
                [ bench "union - union with inverse"
                    $ nf (uncurry NestedValue.union) vals
                , bench "valueContains - is sub-value"
                    $ nf (uncurry NestedValue.valueContains) vals
                ]
        , env setupEnvFlattened1andInv $ \ ~vals ->
            bgroup "FlattenedValue"
                [ bench "union - union with inverse"
                    $ nf (uncurry FlattenedValue.union) vals
                , bench "valueContains - is sub-value"
                    $ nf (uncurry FlattenedValue.valueContains) vals
                ]
        , env setupEnvMM1andInv $ \ ~vals ->
            bgroup "MMValue"
                [ bench "union - union with inverse"
                    $ nf (uncurry MMValue.union) vals
                , bench "valueContains - is sub-value"
                    $ nf (uncurry MMValue.valueContains) vals
                ]
        ]

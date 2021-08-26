{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Benchmarks.Unit (makeBenchmarks) where

import           PlutusCore
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.MkPlc
import           UntypedPlutusCore                      as UPLC

import           Benchmarks.Common

import           Criterion.Main
import           Data.ByteString                        as BS
import           System.Random                          (StdGen)


-- This is a bit painful because chooseUnit is polymorphic and we have to insert a type instantiation.
-- The next couple of functions are adaptations of things in Common.hs, but we'll probably have to
-- extend them for other polymorphic builtins.
mkAppChoose :: forall a . (DefaultUni `Includes` a) =>  Type TyName DefaultUni () -> a -> PlainTerm DefaultFun
mkAppChoose ty x =
    erase $ mkIterApp () (tyInst () (builtin () ChooseUnit) ty) [mkConstant () (),  mkConstant () x]

createChooseUnitBench
    :: (DefaultUni `Includes` a, ExMemoryUsage a)
    => Type TyName DefaultUni ()
    -> [a]
    -> Benchmark
createChooseUnitBench ty xs =
    bgroup (show name) $ [bgroup (showMemoryUsage ()) [mkBM x | x <- xs]]
        where name = ChooseUnit
              mkBM x = benchDefault (showMemoryUsage x) $ mkAppChoose ty x

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = [ createChooseUnitBench integer numbers
                     , createChooseUnitBench bytestring bytestrings ]
    where (numbers, _) = makeSizedIntegers gen (fmap (100 *) [1..50])
          bytestrings = fmap (makeSizedByteString seedA) (fmap (100 *) [51..100])
          integer = mkTyBuiltin @_ @Integer () :: Type TyName DefaultUni ()
          bytestring = mkTyBuiltin @_ @BS.ByteString () :: Type TyName DefaultUni ()
          -- The time should be independent of the type and size of the input,
          -- but let's vary them to make sure.







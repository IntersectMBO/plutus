{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TypeOperators #-}

module Benchmarks.Common
where

import           PlutusCore                                      as PLC
import           PlutusCore.Data
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.Evaluation.Machine.MachineParameters
import           PlutusCore.MkPlc
import           PlutusCore.Pretty                               (Pretty)
import           UntypedPlutusCore                               as UPLC
import           UntypedPlutusCore.Evaluation.Machine.Cek

import           Control.DeepSeq                                 (NFData)
import           Criterion.Main
import qualified Data.ByteString                                 as BS
import           Data.Ix                                         (Ix)
import           Data.Typeable                                   (Typeable)
import           System.Random                                   (StdGen, randomR)


import qualified Hedgehog                                        as H
import qualified Hedgehog.Internal.Gen                           as G
import qualified Hedgehog.Internal.Tree                          as T

type PlainTerm fun = UPLC.Term Name DefaultUni fun ()

showMemoryUsage :: ExMemoryUsage a => a -> String
showMemoryUsage = show . memoryUsage

---------------- Cloning objects ----------------
-- TODO: look at GHC.Compact

{-# NOINLINE incInteger #-}
incInteger :: Integer -> Integer
incInteger n = n+1

{-# NOINLINE decInteger #-}
decInteger :: Integer -> Integer
decInteger n = n-1

{-# NOINLINE copyInteger #-}
copyInteger :: Integer -> Integer
copyInteger = decInteger . incInteger

{-# NOINLINE copyByteString #-}
copyByteString :: BS.ByteString -> BS.ByteString
copyByteString = BS.copy

{-# NOINLINE copyData #-}
copyData :: Data -> Data
copyData =
    \case
     Constr n l -> Constr (copyInteger n) (map copyData l)
     Map l      -> Map $ map (\(a,b) -> (copyData a, copyData b)) l
     List l     -> List (map copyData l)
     I n        -> I $ copyInteger n
     B b        -> B $ copyByteString b


---------------- Creating benchmarks ----------------

-- TODO.  I'm not totally sure what's going on here.  `env` is supposed to
-- produce data that will be supplied to the things being benchmarked.  Here
-- we've got a term and we evaluate it to get back the budget consumed, but then
-- we throw that away and evaluate the term again.  This may have the effect of
-- avoiding warmup, which could be a good thing.  Let's look into that.
benchWith
    :: (Ix fun, NFData fun, Pretty fun, Typeable fun)
    => MachineParameters CekMachineCosts CekValue DefaultUni fun
    -> String
    -> PlainTerm fun
    -> Benchmark
benchWith params name term = env
    (do
        (_result, budget) <-
          pure $ (unsafeEvaluateCek noEmitter params) term
        pure budget
        )
    $ \_ -> bench name $ nf (unsafeEvaluateCek noEmitter params) term

benchDefault :: String -> PlainTerm DefaultFun -> Benchmark
benchDefault = benchWith defaultCekParameters


---------------- Constructing PLC terms for benchmarking ----------------

-- Create a term applying a builtin to one argument
mkApp1 :: (DefaultUni `Includes` a) => fun -> a -> PlainTerm fun
mkApp1 name x =
    erase $ mkIterApp () (builtin () name) [mkConstant () x]


-- Create a term applying a builtin to two arguments
mkApp2
    :: (DefaultUni `Includes` a, DefaultUni `Includes` b)
    =>  fun -> a -> b -> PlainTerm fun
mkApp2 name x y =
    erase $ mkIterApp () (builtin () name) [mkConstant () x,  mkConstant () y]


-- Create a term applying a builtin to three arguments
mkApp3
    :: forall fun a b c. (DefaultUni `Includes` a, DefaultUni `Includes` b, DefaultUni `Includes` c)
    => fun -> a -> b -> c -> PlainTerm fun
mkApp3 name x y z =
    erase $ mkIterApp () (builtin () name) [mkConstant () x,  mkConstant () y, mkConstant () z]


-- Create a term applying a builtin to four arguments
mkApp4
    :: forall fun a b c d. (DefaultUni `Includes` a, DefaultUni `Includes` b, DefaultUni `Includes` c,
                          DefaultUni `Includes` d)
    => fun -> a -> b -> c -> d -> PlainTerm fun
mkApp4 name x y z t =
    erase $ mkIterApp () (builtin () name) [mkConstant () x,  mkConstant () y, mkConstant () z,
                                            mkConstant () t]

-- Create a term applying a builtin to five arguments
mkApp5
    :: forall fun a b c d e. (DefaultUni `Includes` a, DefaultUni `Includes` b, DefaultUni `Includes` c,
                                DefaultUni `Includes` d, DefaultUni `Includes` e)
    => fun -> a -> b -> c -> d -> e -> PlainTerm fun
mkApp5 name x y z t u =
    erase $ mkIterApp () (builtin () name) [mkConstant () x, mkConstant () y, mkConstant () z,
                                            mkConstant () t, mkConstant () u]

-- Create a term applying a builtin to six arguments
mkApp6
    :: forall fun a b c d e f. (DefaultUni `Includes` a, DefaultUni `Includes` b, DefaultUni `Includes` c,
                                DefaultUni `Includes` d, DefaultUni `Includes` e, DefaultUni `Includes` f)
    => fun -> a -> b -> c -> d -> e -> f-> PlainTerm fun
mkApp6 name x y z t u v =
    erase $ mkIterApp () (builtin () name) [mkConstant () x, mkConstant () y, mkConstant () z,
                                            mkConstant () t, mkConstant () u, mkConstant () v]


---------------- Creating benchmarks ----------------

{- | The use of bgroups in the functions below will cause Criterion to give the
   benchmarks names like "AddInteger/ExMemory 11/ExMemory 5": these are saved in
   the CSV file and the 'benchData' function in 'models.R' subsequently extracts
   the names and memory figures for use as entries in the data frame used to
   generate the cost models.  Hence changing the nesting of the bgroups would
   cause trouble elsewhere.
 -}

integerPower :: Integer -> Integer -> Integer
integerPower = (^) -- Just to avoid some type ascriptions later

{- | Given a builtin function f of type a -> _ together with a lists xs::[a]
   (along with their memory sizes), create a collection of benchmarks which run
   f on all elements of xs. -}
createOneTermBuiltinBench
    :: (DefaultUni `Includes` a, ExMemoryUsage a)
    => DefaultFun
    -> [a]
    -> Benchmark
createOneTermBuiltinBench name xs =
    bgroup (show name) $ [mkBM x | x <- xs]
        where mkBM x = benchDefault (showMemoryUsage x) $ mkApp1 name x

{- | Given a builtin function f of type a * b -> _ together with lists xs::[a] and
   ys::[b] (along with their memory sizes), create a collection of benchmarks
   which run f on all pairs in {(x,y}: x in xs, y in ys}. -}
createTwoTermBuiltinBench
    :: (DefaultUni `Includes` a, DefaultUni `Includes` b, ExMemoryUsage a, ExMemoryUsage b)
    => DefaultFun
    -> [a]
    -> [b]
    -> Benchmark
createTwoTermBuiltinBench name xs ys =
    bgroup (show name) $ [bgroup (showMemoryUsage x) [mkBM x y | y <- ys] | x <- xs]
        where mkBM x y = benchDefault (showMemoryUsage y) $ mkApp2 name x y

{- | Given a builtin function f of type a * b -> _ together with lists xs::a and
   ys::a (along with their memory sizes), create a collection of benchmarks
   which run f on all pairs in 'zip xs ys'.  This can be used when the
   worst-case execution time of a two-argument builtin is known to occur when it
   is given two identical arguments (for example equality testing, where the
   function has to examine the whole of both inputs in that case; with unequal
   arguments it will usually be able to return more quickly).  The caller may
   wish to ensure that the elements of the two lists are physically different to
   avoid early return if a builtin can spot that its arguments both point to the
   same heap object.
-}
createTwoTermBuiltinBenchElementwise
    :: (DefaultUni `Includes` a, DefaultUni `Includes` b, ExMemoryUsage a, ExMemoryUsage b)
    => DefaultFun
    -> [a]
    -> [b]
    -> Benchmark
createTwoTermBuiltinBenchElementwise name xs ys =
    bgroup (show name) $ zipWith (\x y -> bgroup (showMemoryUsage x) [mkBM x y]) xs ys
        where mkBM x y = benchDefault (showMemoryUsage y) $ mkApp2 name x y
-- TODO: throw an error if xmem != ymem?  That would suggest that the caller has
-- done something wrong.

-- Generate a random n-word (ie, 64n-bit) integer
{- In principle a random 5-word integer (for example) might only occupy 4 or
   fewer words, but we're generating uniformly distributed values so the
   probability of that happening should be at most 1 in 2^64. -}
randNwords :: Integer -> StdGen -> (Integer, StdGen)
randNwords n gen = randomR (lb,ub) gen
    where lb = 2^(64*(n-1))
          ub = 2^(64*n) - 1

{- TODO: we're using Hedgehog for some things and System.Random for others.  We
   should rationalise this.  Pehaps Hedgehog is more future-proof since it can
   produce random instances of a wide variety of types.  On the other hand, you
   have to be careful with Hedgehog Ranges since they don't necessarily do what
   you might expect.  It might be a bit tricky to use Hedgehog everywhere
   because we'd need a lot of monadic code to take care of generator states. -}
genSample :: H.Seed -> G.Gen a -> a
genSample seed gen = Prelude.maybe (Prelude.error "Couldn't create a sample") T.treeValue $ G.evalGen (H.Size 1) seed gen

powersOfTwo :: [Integer]
powersOfTwo = integerPower 2 <$> [1..16]

-- Make some really big numbers for benchmarking
threeToThePower :: Integer -> Integer
threeToThePower e = integerPower 3 e

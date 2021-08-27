{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Benchmarks.Common
where

import           PlutusCore
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
import qualified Hedgehog.Internal.Range                         as R
import qualified Hedgehog.Internal.Tree                          as T

type PlainTerm uni fun = UPLC.Term Name uni fun ()

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
    -> PlainTerm DefaultUni fun
    -> Benchmark
benchWith params name term = env
    (do
        (_result, budget) <-
          pure $ (unsafeEvaluateCek noEmitter params) term
        pure budget
        )
    $ \_ -> bench name $ nf (unsafeEvaluateCek noEmitter params) term

benchDefault :: String -> PlainTerm DefaultUni DefaultFun -> Benchmark
benchDefault = benchWith defaultCekParameters


---------------- Constructing Polymorphic PLC terms for benchmarking ----------------

integer :: uni `Includes` Integer => Type tyname uni ()
integer = mkTyBuiltin @_ @Integer ()

bytestring :: uni `Includes` BS.ByteString => Type tyname uni ()
bytestring = mkTyBuiltin @_ @BS.ByteString ()


-- To make monomorhpic terms, make tys equal to [] in the mkApp functions

-- Create a term instantiating a builtin and applying it to one argument
mkApp1 :: (uni `Includes` a) => fun -> [Type tyname uni ()] -> a -> PlainTerm uni fun
mkApp1 name tys x =
    erase $ mkIterApp () instantiated [mkConstant () x]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to two arguments
mkApp2
    :: (uni `Includes` a, uni `Includes` b)
    =>  fun -> [Type tyname uni ()]-> a -> b -> PlainTerm uni fun
mkApp2 name tys x y =
    erase $ mkIterApp () instantiated [mkConstant () x,  mkConstant () y]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to three arguments
mkApp3
    :: (uni `Includes` a, uni `Includes` b, uni `Includes` c)
    => fun -> [Type tyname uni ()] -> a -> b -> c -> PlainTerm uni fun
mkApp3 name tys x y z =
    erase $ mkIterApp () instantiated [mkConstant () x, mkConstant () y, mkConstant () z]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to four arguments
mkApp4
    :: (uni `Includes` a, uni `Includes` b,
        uni `Includes` c, uni `Includes` d)
    => fun -> [Type tyname uni ()] -> a -> b -> c -> d -> PlainTerm uni fun
mkApp4 name tys x y z t =
    erase $ mkIterApp () instantiated [ mkConstant () x, mkConstant () y
                                      , mkConstant () z, mkConstant () t ]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to five arguments
mkApp5
    :: (uni `Includes` a, uni `Includes` b, uni `Includes` c,
        uni `Includes` d, uni `Includes` e)
    => fun -> [Type tyname uni ()] -> a -> b -> c -> d -> e -> PlainTerm uni fun
mkApp5 name tys x y z t u =
    erase $ mkIterApp () instantiated [ mkConstant () x, mkConstant () y, mkConstant () z
                                      , mkConstant () t, mkConstant () u ]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to six arguments
mkApp6
    :: (uni `Includes` a, uni `Includes` b, uni `Includes` c,
        uni `Includes` d, uni `Includes` e, uni `Includes` f)
    => fun -> [Type tyname uni ()] -> a -> b -> c -> d -> e -> f-> PlainTerm uni fun
mkApp6 name tys x y z t u v =
    erase $ mkIterApp () instantiated [mkConstant () x, mkConstant () y, mkConstant () z,
                                       mkConstant () t, mkConstant () u, mkConstant () v]
    where instantiated = mkIterInst () (builtin () name) tys


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
        where mkBM x = benchDefault (showMemoryUsage x) $ mkApp1 name [] x

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
        where mkBM x y = benchDefault (showMemoryUsage y) $ mkApp2 name [] x y

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
        where mkBM x y = benchDefault (showMemoryUsage y) $ mkApp2 name [] x y
-- TODO: throw an error if xmem != ymem?  That would suggest that the caller has
-- done something wrong.

-- Generate a random n-word (ie, 64n-bit) integer
{- In principle a random 5-word integer (for example) might only occupy 4 or
   fewer words, but we're generating uniformly distributed values so the
   probability of that happening should be at most 1 in 2^64. -}
randNwords :: StdGen -> Int -> (Integer, StdGen)
randNwords gen n = randomR (lb,ub) gen
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


---------------- Creating things of a given size ----------------

seedA :: H.Seed
seedA = H.Seed 42 43

seedB :: H.Seed
seedB = H.Seed 44 45

-- Given a list [n_1, n_2, ...] create a list [m_1, m_2, ...] where m_i is an n_i-word random integer
makeSizedIntegers :: StdGen -> [Int] -> ([Integer], StdGen)
makeSizedIntegers g [] = ([], g)
makeSizedIntegers g (n:ns) =
    let (m,g1) = randNwords g n
        (ms,g2) = makeSizedIntegers g1 ns
    in (m:ms,g2)

-- Create a bytestring whose memory usage is n.  Since we measure memory usage
-- in 64-bit words we have to create a bytestring containing 8*n bytes.
makeSizedByteString :: H.Seed -> Int -> BS.ByteString
makeSizedByteString seed n = genSample seed (G.bytes (R.singleton (8*n)))

-- FIXME: this is terrible
makeSizedByteStrings :: H.Seed -> [Int] -> [BS.ByteString]
makeSizedByteStrings seed l = map (makeSizedByteString seed) l

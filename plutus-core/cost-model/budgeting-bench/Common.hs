{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE ViewPatterns     #-}

module Common
where

import PlutusCore
import PlutusCore.Data
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.MkPlc
import PlutusCore.Pretty (Pretty)
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.DeepSeq (NFData, force)
import Criterion.Main
import Data.ByteString qualified as BS
import Data.Ix (Ix)
import Data.Typeable (Typeable)

type PlainTerm uni fun = UPLC.Term Name uni fun ()

showMemoryUsage :: ExMemoryUsage a => a -> String
showMemoryUsage = show . memoryUsage

---------------- Cloning objects ----------------
-- TODO: look at GHC.Compact

{- | In some cases (for example, equality testing) the worst-case behaviour of a
builtin will be when it has two identical arguments However, there's a danger
that if the arguments are physically identical (ie, they are (pointers to) the
same object in the heap) the underlying implementation may notice that and
return immediately.  The code below attempts to avoid this by producing a
completely new copy of an integer.  Experiments with 'realyUnsafePtrEquality#`
indicate that it does what's required (in fact, `cloneInteger n = (n+1)-1` with
NOINLINE suffices, but that's perhaps a bit too fragile).
-}

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

benchWith
    :: (Ix fun, Pretty fun, Typeable fun)
    => MachineParameters CekMachineCosts CekValue DefaultUni fun
    -> String
    -> PlainTerm DefaultUni fun
    -> Benchmark
benchWith params name term = bench name $ whnf (unsafeEvaluateCekNoEmit params) term
{- ^ Note that to get sensible results with whnf, we must use an evaluation
   function that looks at the result, so eg unsafeEvaluateCek won't work
   properly because it returns a pair whose components won't be evaluated by
   whnf.  We can't use nf because it does too much work: for instance if it gets
   back a 'Data' value it'll traverse all of it.
-}

benchDefault :: String -> PlainTerm DefaultUni DefaultFun -> Benchmark
benchDefault = benchWith defaultCekParameters


---------------- Constructing Polymorphic PLC terms for benchmarking ----------------

integer :: uni `Includes` Integer => Type tyname uni ()
integer = mkTyBuiltin @_ @Integer ()

bytestring :: uni `Includes` BS.ByteString => Type tyname uni ()
bytestring = mkTyBuiltin @_ @BS.ByteString ()


-- To make monomorhpic terms, make tys equal to [] in the mkApp functions

-- Create a term instantiating a builtin and applying it to one argument
mkApp1 :: (uni `Includes` a, NFData a) => fun -> [Type tyname uni ()] -> a -> PlainTerm uni fun
mkApp1 !name !tys (force -> !x) =
    erase $ mkIterApp () instantiated [mkConstant () x]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to two arguments
mkApp2
    :: (uni `Includes` a, uni `Includes` b, NFData a, NFData b)
    =>  fun -> [Type tyname uni ()]-> a -> b -> PlainTerm uni fun
mkApp2 !name !tys (force -> !x) (force -> !y) =
    erase $ mkIterApp () instantiated [mkConstant () x,  mkConstant () y]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to three arguments
mkApp3
    :: (uni `Includes` a, uni `Includes` b, uni `Includes` c, NFData a, NFData b, NFData c)
    => fun -> [Type tyname uni ()] -> a -> b -> c -> PlainTerm uni fun
mkApp3 !name !tys (force -> !x) (force -> !y) (force -> !z) =
    erase $ mkIterApp () instantiated [mkConstant () x, mkConstant () y, mkConstant () z]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to four arguments
mkApp4
    :: (uni `Includes` a, uni `Includes` b,
        uni `Includes` c, uni `Includes` d,
        NFData a, NFData b, NFData c, NFData d)
    => fun -> [Type tyname uni ()] -> a -> b -> c -> d -> PlainTerm uni fun
mkApp4 !name !tys (force -> !x) (force -> !y) (force -> !z) (force -> !t) =
    erase $ mkIterApp () instantiated [ mkConstant () x, mkConstant () y
                                      , mkConstant () z, mkConstant () t ]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to five arguments
mkApp5
    :: (uni `Includes` a, uni `Includes` b, uni `Includes` c,
        uni `Includes` d, uni `Includes` e,
        NFData a, NFData b, NFData c, NFData d, NFData e)
    => fun -> [Type tyname uni ()] -> a -> b -> c -> d -> e -> PlainTerm uni fun
mkApp5 !name !tys (force -> !x) (force -> !y) (force -> !z) (force -> !t) (force -> !u) =
    erase $ mkIterApp () instantiated [ mkConstant () x, mkConstant () y, mkConstant () z
                                      , mkConstant () t, mkConstant () u ]
    where instantiated = mkIterInst () (builtin () name) tys


-- Create a term instantiating a builtin and applying it to six arguments
mkApp6
    :: (uni `Includes` a, uni `Includes` b, uni `Includes` c,
        uni `Includes` d, uni `Includes` e, uni `Includes` f,
        NFData a, NFData b, NFData c, NFData d, NFData e, NFData f)
    => fun -> [Type tyname uni ()] -> a -> b -> c -> d -> e -> f-> PlainTerm uni fun
mkApp6 name tys (force -> !x) (force -> !y) (force -> !z) (force -> !t) (force -> !u) (force -> !v) =
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

{- | Given a builtin function f of type a -> _ together with a lists xs, create a
   collection of benchmarks which run f on all elements of xs. -}
createOneTermBuiltinBench
    :: (fun ~ DefaultFun, uni ~ DefaultUni, uni `Includes` a, ExMemoryUsage a, NFData a)
    => fun
    -> [Type tyname uni ()]
    -> [a]
    -> Benchmark
createOneTermBuiltinBench name tys xs =
    bgroup (show name) $ [mkBM x | x <- xs]
        where mkBM x = benchDefault (showMemoryUsage x) $ mkApp1 name tys x

{- | Given a builtin function f of type a * b -> _ together with lists xs::[a] and
   ys::[b], create a collection of benchmarks which run f on all pairs in
   {(x,y}: x in xs, y in ys}. -}
createTwoTermBuiltinBench
    :: (fun ~ DefaultFun, uni ~ DefaultUni, uni `Includes` a, DefaultUni `Includes` b,
        ExMemoryUsage a, ExMemoryUsage b, NFData a, NFData b)
    => fun
    -> [Type tyname uni ()]
    -> [a]
    -> [b]
    -> Benchmark
createTwoTermBuiltinBench name tys xs ys =
    bgroup (show name) $ [bgroup (showMemoryUsage x) [mkBM x y | y <- ys] | x <- xs]
        where mkBM x y = benchDefault (showMemoryUsage y) $ mkApp2 name tys x y

{- | Given a builtin function f of type a * b -> _ together with lists xs::[a] and
   ys::[b], create a collection of benchmarks which run f on all pairs in 'zip
   xs ys'.  This can be used when the worst-case execution time of a
   two-argument builtin is known to occur when it is given two identical
   arguments (for example equality testing, where the function has to examine
   the whole of both inputs in that case; with unequal arguments it will usually
   be able to return more quickly).  The caller may wish to ensure that the
   elements of the two lists are physically different to avoid early return if a
   builtin can spot that its arguments both point to the same heap object.
-}
createTwoTermBuiltinBenchElementwise
    :: (fun ~ DefaultFun, uni ~ DefaultUni, uni `Includes` a, uni `Includes` b,
            ExMemoryUsage a, ExMemoryUsage b, NFData a, NFData b)
    => fun
    -> [Type tyname uni ()]
    -> [a]
    -> [b]
    -> Benchmark
createTwoTermBuiltinBenchElementwise name tys xs ys =
    bgroup (show name) $ zipWith (\x y -> bgroup (showMemoryUsage x) [mkBM x y]) xs ys
        where mkBM x y = benchDefault (showMemoryUsage y) $ mkApp2 name tys x y
-- TODO: throw an error if xmem != ymem?  That would suggest that the caller has
-- done something wrong.

{- | Given a builtin function f of type a * b * c -> _ together with lists
   xs::[a], ys::[b], and zs::[c], create a collection of benchmarks which run f
   on all pairs in 'zip3 xs ys zs'.
-}
createThreeTermBuiltinBenchElementwise
    :: (fun ~ DefaultFun, uni ~ DefaultUni, uni `Includes` a, uni `Includes` b, uni `Includes` c,
            ExMemoryUsage a, ExMemoryUsage b, ExMemoryUsage c, NFData a, NFData b, NFData c)
    => fun
    -> [Type tyname uni ()]
    -> [a]
    -> [b]
    -> [c]
    -> Benchmark
createThreeTermBuiltinBenchElementwise name tys xs ys zs =
    bgroup (show name) $ zipWith3 (\x y z -> bgroup (showMemoryUsage x) [bgroup (showMemoryUsage y) [mkBM x y z]]) xs ys zs
        where mkBM x y z = benchDefault (showMemoryUsage z) $ mkApp3 name tys x y z
-- TODO: throw an error if xmem != ymem?  That would suggest that the caller has
-- done something wrong.

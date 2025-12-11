{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Common
where

import PlutusCore hiding (Constr)
import PlutusCore.Compiler.Erase
import PlutusCore.Data
import PlutusCore.Evaluation.Machine.CostStream (sumCostStream)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn, mkIterInstNoAnn, mkTyBuiltin)
import PlutusCore.Pretty (Pretty, display)
import UntypedPlutusCore as UPLC hiding (Constr)
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.DeepSeq (NFData, force)
import Criterion.Main (Benchmark, bench, bgroup, whnf)
import Data.Bifunctor (bimap)
import Data.ByteString qualified as BS
import Data.Text qualified as T
import Data.Typeable (Typeable)

type PlainTerm uni fun = UPLC.Term Name uni fun ()

showMemoryUsage :: ExMemoryUsage a => a -> String
showMemoryUsage = show . sumCostStream . flattenCostRose . memoryUsage

---------------- Cloning objects ----------------
-- TODO: look at GHC.Compact

{-| In some cases (for example, equality testing) the worst-case behaviour of a
builtin will be when it has two identical arguments However, there's a danger
that if the arguments are physically identical (ie, they are (pointers to) the
same object in the heap) the underlying implementation may notice that and
return immediately.  The code below attempts to avoid this by producing a
completely new copy of an integer.  Experiments with 'realyUnsafePtrEquality#`
indicate that it does what's required (in fact, `cloneInteger n = (n+1)-1` with
OPAQUE suffices, but that's perhaps a bit too fragile). -}
incInteger :: Integer -> Integer
incInteger n = n + 1
{-# OPAQUE incInteger #-}

decInteger :: Integer -> Integer
decInteger n = n - 1
{-# OPAQUE decInteger #-}

copyInteger :: Integer -> Integer
copyInteger = decInteger . incInteger
{-# OPAQUE copyInteger #-}

copyByteString :: BS.ByteString -> BS.ByteString
copyByteString = BS.copy
{-# OPAQUE copyByteString #-}

copyData :: Data -> Data
copyData =
  \case
    Constr n l -> Constr (copyInteger n) (map copyData l)
    Map l -> Map $ map (bimap copyData copyData) l
    List l -> List (map copyData l)
    I n -> I $ copyInteger n
    B b -> B $ copyByteString b
{-# OPAQUE copyData #-}

pairWith :: (a -> b) -> [a] -> [(a, b)]
pairWith f = fmap (\a -> (a, f a))

---------------- Creating benchmarks ----------------

benchWith
  :: forall fun
   . (Pretty fun, Typeable fun)
  => MachineParameters CekMachineCosts fun (CekValue DefaultUni fun ())
  -> String
  -> PlainTerm DefaultUni fun
  -> Benchmark
-- Note that to get sensible results with 'whnf', we must use an evaluation function that looks at
-- the result, so e.g. 'evaluateCek' won't work properly because it returns a pair whose components
-- won't be evaluated by 'whnf'. We can't use 'nf' because it does too much work: for instance if it
-- gets back a 'Data' value it'll traverse all of it.
benchWith params name term =
  bench name $
    whnf (runEvalCek params) term
  where
    runEvalCek
      :: MachineParameters CekMachineCosts fun (CekValue DefaultUni fun ())
      -> PlainTerm DefaultUni fun
      -> PlainTerm DefaultUni fun
    runEvalCek ps t =
      let (result, logs) = evaluateCek logEmitter ps t
       in case result of
            Right res -> res
            Left (ErrorWithCause err cause) ->
              error $
                "Evaluation error:\n" ++ show err ++ "\nCaused by:\n" ++ display cause <> "\nLogs:\n" ++ unlines (map T.unpack logs)

{- Benchmark with the most recent CekParameters -}
benchDefault :: String -> PlainTerm DefaultUni DefaultFun -> Benchmark
benchDefault = benchWith defaultCekParametersForTesting

---------------- Constructing Polymorphic PLC terms for benchmarking ----------------

integer :: uni `HasTypeLevel` Integer => Type TyName uni ()
integer = mkTyBuiltin @_ @Integer ()

bytestring :: uni `HasTypeLevel` BS.ByteString => Type TyName uni ()
bytestring = mkTyBuiltin @_ @BS.ByteString ()

-- To make monomorphic terms, make tys equal to [] in the mkApp functions

-- Just make the term (con unit ()), which is about the simplest possible.
mkUnit :: uni `HasTermLevel` () => PlainTerm uni fun
mkUnit = eraseTerm $ mkConstant () ()

-- Create a term instantiating a builtin and applying it to one argument
mkApp1
  :: (uni `HasTermLevel` a, NFData a)
  => fun -> [Type tyname uni ()] -> a -> PlainTerm uni fun
mkApp1 !fun !tys (force -> !x) =
  eraseTerm $ mkIterAppNoAnn instantiated [mkConstant () x]
  where
    instantiated = mkIterInstNoAnn (builtin () fun) tys

-- Create a term instantiating a builtin and applying it to two arguments
mkApp2
  :: (uni `HasTermLevel` a, uni `HasTermLevel` b, NFData a, NFData b)
  => fun -> [Type tyname uni ()] -> a -> b -> PlainTerm uni fun
mkApp2 !fun !tys (force -> !x) (force -> !y) =
  eraseTerm $ mkIterAppNoAnn instantiated [mkConstant () x, mkConstant () y]
  where
    instantiated = mkIterInstNoAnn (builtin () fun) tys

-- Create a term instantiating a builtin and applying it to three arguments
mkApp3
  :: ( uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , uni `HasTermLevel` c
     , NFData a
     , NFData b
     , NFData c
     )
  => fun -> [Type tyname uni ()] -> a -> b -> c -> PlainTerm uni fun
mkApp3 !fun !tys (force -> !x) (force -> !y) (force -> !z) =
  eraseTerm $ mkIterAppNoAnn instantiated [mkConstant () x, mkConstant () y, mkConstant () z]
  where
    instantiated = mkIterInstNoAnn (builtin () fun) tys

-- Create a term instantiating a builtin and applying it to four arguments
mkApp4
  :: ( uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , uni `HasTermLevel` c
     , uni `HasTermLevel` d
     , NFData a
     , NFData b
     , NFData c
     , NFData d
     )
  => fun -> [Type tyname uni ()] -> a -> b -> c -> d -> PlainTerm uni fun
mkApp4 !fun !tys (force -> !x) (force -> !y) (force -> !z) (force -> !t) =
  eraseTerm $
    mkIterAppNoAnn
      instantiated
      [ mkConstant () x
      , mkConstant () y
      , mkConstant () z
      , mkConstant () t
      ]
  where
    instantiated = mkIterInstNoAnn (builtin () fun) tys

-- Create a term instantiating a builtin and applying it to five arguments
mkApp5
  :: ( uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , uni `HasTermLevel` c
     , uni `HasTermLevel` d
     , uni `HasTermLevel` e
     , NFData a
     , NFData b
     , NFData c
     , NFData d
     , NFData e
     )
  => fun -> [Type tyname uni ()] -> a -> b -> c -> d -> e -> PlainTerm uni fun
mkApp5 !fun !tys (force -> !x) (force -> !y) (force -> !z) (force -> !t) (force -> !u) =
  eraseTerm $
    mkIterAppNoAnn
      instantiated
      [ mkConstant () x
      , mkConstant () y
      , mkConstant () z
      , mkConstant () t
      , mkConstant () u
      ]
  where
    instantiated = mkIterInstNoAnn (builtin () fun) tys

-- Create a term instantiating a builtin and applying it to six arguments
mkApp6
  :: ( uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , uni `HasTermLevel` c
     , uni `HasTermLevel` d
     , uni `HasTermLevel` e
     , uni `HasTermLevel` f
     , NFData a
     , NFData b
     , NFData c
     , NFData d
     , NFData e
     , NFData f
     )
  => fun -> [Type tyname uni ()] -> a -> b -> c -> d -> e -> f -> PlainTerm uni fun
mkApp6 fun tys (force -> !x) (force -> !y) (force -> !z) (force -> !t) (force -> !u) (force -> !v) =
  eraseTerm $
    mkIterAppNoAnn
      instantiated
      [ mkConstant () x
      , mkConstant () y
      , mkConstant () z
      , mkConstant () t
      , mkConstant () u
      , mkConstant () v
      ]
  where
    instantiated = mkIterInstNoAnn (builtin () fun) tys

---------------- Creating benchmarks ----------------

{-| The use of bgroups in the functions below will cause Criterion to give the
   benchmarks names like "AddInteger/ExMemory 11/ExMemory 5": these are saved in
   the CSV file and the 'benchData' function in 'models.R' subsequently extracts
   the names and memory figures for use as entries in the data frame used to
   generate the cost models.  Hence changing the nesting of the bgroups would
   cause trouble elsewhere. -}
{-| Given a builtin function f of type a -> _ together with a lists xs, create a
   collection of benchmarks which run f on all elements of xs. -}
createOneTermBuiltinBench
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , ExMemoryUsage a
     , NFData a
     )
  => fun
  -> [Type tyname uni ()]
  -> [a]
  -> Benchmark
createOneTermBuiltinBench = createOneTermBuiltinBenchWithWrapper id

{- Note [Adjusting the memory usage of arguments of costing benchmarks] In some
  cases we want to measure the (so-called) "memory usage" of a builtin argument
  in a nonstandard way for benchmarking and costing purposes. This function
  allows you to supply suitable wrapping functions in the benchmarks to achieve
  this.  NB: wrappers used in benchmarks *MUST* be the same as wrappers used in
  builtin denotations to make sure that during script execution the inputs to
  the costing functions are costed in the same way as the are in thhe
  benchmmarks.
-}
createOneTermBuiltinBenchWithWrapper
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , ExMemoryUsage a'
     , NFData a
     )
  => (a -> a')
  -> fun
  -> [Type tyname uni ()]
  -> [a]
  -> Benchmark
createOneTermBuiltinBenchWithWrapper wrapX fun tys xs =
  bgroup
    (show fun)
    [ benchDefault (showMemoryUsage (wrapX x)) (mkApp1 fun tys x)
    | x <- xs
    ]

{-| Given a builtin function f of type a * b -> _ together with lists xs::[a] and
   ys::[b], create a collection of benchmarks which run f on all pairs in
   {(x,y}: x in xs, y in ys}. -}
createTwoTermBuiltinBench
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , ExMemoryUsage a
     , ExMemoryUsage b
     , NFData a
     , NFData b
     )
  => fun
  -> [Type tyname uni ()]
  -> [a]
  -> [b]
  -> Benchmark
createTwoTermBuiltinBench fun tys xs ys =
  bgroup (show fun) [bgroup (showMemoryUsage x) [mkBM x y | y <- ys] | x <- xs]
  where
    mkBM x y = benchDefault (showMemoryUsage y) $ mkApp2 fun tys x y

createTwoTermBuiltinBenchWithFlag
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , ExMemoryUsage a
     , ExMemoryUsage b
     , NFData a
     , NFData b
     )
  => fun
  -> [Type tyname uni ()]
  -> Bool
  -> [a]
  -> [b]
  -> Benchmark
createTwoTermBuiltinBenchWithFlag fun tys flag ys zs =
  bgroup
    (show fun)
    [ bgroup
        (showMemoryUsage flag)
        [bgroup (showMemoryUsage y) [mkBM y z | z <- zs] | y <- ys]
    ]
  where
    mkBM y z = benchDefault (showMemoryUsage z) $ mkApp3 fun tys flag y z

{-| Given a builtin function f of type a * b -> _ together with lists xs::[a] and
   ys::[b], create a collection of benchmarks which run f on all pairs in
   {(x,y}: x in xs, y in ys}. -}
createTwoTermBuiltinBenchWithWrappers
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , ExMemoryUsage a'
     , ExMemoryUsage b'
     , NFData a
     , NFData b
     )
  => (a -> a', b -> b')
  -> fun
  -> [Type tyname uni ()]
  -> [a]
  -> [b]
  -> Benchmark
createTwoTermBuiltinBenchWithWrappers (wrapX, wrapY) fun tys xs ys =
  bgroup (show fun) [bgroup (showMemoryUsage (wrapX x)) [mkBM x y | y <- ys] | x <- xs]
  where
    mkBM x y = benchDefault (showMemoryUsage (wrapY y)) $ mkApp2 fun tys x y

{-| Given a builtin function f of type a * b -> _ together with a list of (a,b)
   pairs, create a collection of benchmarks which run f on all of the pairs in
   the list.  This can be used when the worst-case execution time of a
   two-argument builtin is known to occur when it is given two identical
   arguments (for example equality testing, where the function has to examine
   the whole of both inputs in that case; with unequal arguments it will usually
   be able to return more quickly).  The caller may wish to ensure that the
   elements of the two lists are physically different to avoid early return if a
   builtin can spot that its arguments both point to the same heap object. -}
createTwoTermBuiltinBenchElementwise
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , ExMemoryUsage a
     , ExMemoryUsage b
     , NFData a
     , NFData b
     )
  => fun
  -> [Type tyname uni ()]
  -> [(a, b)]
  -> Benchmark
createTwoTermBuiltinBenchElementwise =
  createTwoTermBuiltinBenchElementwiseWithWrappers (id, id)

-- TODO: throw an error if xmem != ymem?  That would suggest that the caller has
-- done something wrong.

{- See Note [Adjusting the memory usage of arguments of costing benchmarks]. -}
createTwoTermBuiltinBenchElementwiseWithWrappers
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , ExMemoryUsage a'
     , ExMemoryUsage b'
     , NFData a
     , NFData b
     )
  => (a -> a', b -> b')
  -> fun
  -> [Type tyname uni ()]
  -> [(a, b)]
  -> Benchmark
createTwoTermBuiltinBenchElementwiseWithWrappers (wrapX, wrapY) fun tys inputs =
  bgroup (show fun) $
    fmap (\(x, y) -> bgroup (showMemoryUsage $ wrapX x) [mkBM x y]) inputs
  where
    mkBM x y = benchDefault (showMemoryUsage $ wrapY y) $ mkApp2 fun tys x y

{-| Given a builtin function f of type a * b * c -> _ together with a list of
   inputs of type (a,b,c), create a collection of benchmarks which run f on all
   inputs. -}
createThreeTermBuiltinBenchElementwise
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , uni `HasTermLevel` c
     , ExMemoryUsage a
     , ExMemoryUsage b
     , ExMemoryUsage c
     , NFData a
     , NFData b
     , NFData c
     )
  => fun
  -> [Type tyname uni ()]
  -> [(a, b, c)]
  -> Benchmark
createThreeTermBuiltinBenchElementwise =
  createThreeTermBuiltinBenchElementwiseWithWrappers (id, id, id)

{- See Note [Adjusting the memory usage of arguments of costing benchmarks]. -}
createThreeTermBuiltinBenchElementwiseWithWrappers
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , uni `HasTermLevel` c
     , ExMemoryUsage a'
     , ExMemoryUsage b'
     , ExMemoryUsage c'
     , NFData a
     , NFData b
     , NFData c
     )
  => (a -> a', b -> b', c -> c')
  -> fun
  -> [Type tyname uni ()]
  -> [(a, b, c)]
  -> Benchmark
createThreeTermBuiltinBenchElementwiseWithWrappers (wrapX, wrapY, wrapZ) fun tys inputs =
  bgroup (show fun) $
    fmap
      ( \(x, y, z) ->
          bgroup
            (showMemoryUsage $ wrapX x)
            [bgroup (showMemoryUsage $ wrapY y) [mkBM x y z]]
      )
      inputs
  where
    mkBM x y z = benchDefault (showMemoryUsage $ wrapZ z) $ mkApp3 fun tys x y z

createThreeTermBuiltinBenchWithWrappers
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , uni `HasTermLevel` c
     , ExMemoryUsage a'
     , ExMemoryUsage b'
     , ExMemoryUsage c'
     , NFData a
     , NFData b
     , NFData c
     )
  => (a -> a', b -> b', c -> c')
  -> fun
  -> [Type tyname uni ()]
  -> [a]
  -> [b]
  -> [c]
  -> Benchmark
createThreeTermBuiltinBenchWithWrappers (wrapX, wrapY, wrapZ) fun tys xs ys zs =
  bgroup
    (show fun)
    [ bgroup
        (showMemoryUsage (wrapX x))
        [ bgroup
            (showMemoryUsage (wrapY y))
            [mkBM x y z | z <- zs]
        | y <- ys
        ]
    | x <- xs
    ]
  where
    mkBM x y z = benchDefault (showMemoryUsage (wrapZ z)) $ mkApp3 fun tys x y z

{- See Note [Adjusting the memory usage of arguments of costing benchmarks]. -}
createFourTermBuiltinBenchElementwiseWithWrappers
  :: ( fun ~ DefaultFun
     , uni ~ DefaultUni
     , uni `HasTermLevel` a
     , uni `HasTermLevel` b
     , uni `HasTermLevel` c
     , uni `HasTermLevel` d
     , ExMemoryUsage a'
     , ExMemoryUsage b'
     , ExMemoryUsage c'
     , ExMemoryUsage d'
     , NFData a
     , NFData b
     , NFData c
     , NFData d
     )
  => (a -> a', b -> b', c -> c', d -> d')
  -> fun
  -> [Type tyname uni ()]
  -> [(a, b, c, d)]
  -> Benchmark
createFourTermBuiltinBenchElementwiseWithWrappers (wrapW, wrapX, wrapY, wrapZ) fun tys inputs =
  bgroup (show fun) $
    fmap
      ( \(w, x, y, z) ->
          bgroup
            (showMemoryUsage $ wrapW w)
            [ bgroup
                (showMemoryUsage $ wrapX x)
                [bgroup (showMemoryUsage $ wrapY y) [mkBM w x y z]]
            ]
      )
      inputs
  where
    mkBM w x y z = benchDefault (showMemoryUsage $ wrapZ z) $ mkApp4 fun tys w x y z

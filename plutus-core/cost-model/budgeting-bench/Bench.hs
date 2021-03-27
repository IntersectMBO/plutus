{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

-- See Note [Creation of the Cost Model]
module Main (main) where

import           PlutusCore                               as PLC
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.MkPlc
import           UntypedPlutusCore                        as UPLC
import           UntypedPlutusCore.Evaluation.Machine.Cek

import           Criterion.Main
import qualified Criterion.Types                          as C
import qualified Data.ByteString                          as BS
import           Data.Functor
import qualified Hedgehog                                 as HH
import qualified Hedgehog.Internal.Gen                    as HH
import qualified Hedgehog.Internal.Tree                   as HH
import qualified Hedgehog.Range                           as HH.Range
import           System.Directory
import           System.FilePath
import           System.Random                            (StdGen, getStdGen, randomR)

type PlainTerm = UPLC.Term Name DefaultUni DefaultFun ()

-- TODO.  I'm not totally sure what's going on here.  `env` is supposed to
-- produce data that will be supplied to the things being benchmarked.  Here
-- we've got a term and we evaluate it to get back the budget consumed, but then
-- we throw that away and evaluate the term again.  This may have the effect of
-- avoiding warmup, which could be a good thing.  Let's look into that.
runTermBench :: String -> PlainTerm -> Benchmark
runTermBench name term = env
    (do
        (_result, budget) <-
          pure $ (unsafeEvaluateCek defBuiltinsRuntime) term
        pure budget
        )
    $ \_ -> bench name $ nf (unsafeEvaluateCek defBuiltinsRuntime) term


---------------- Constructing PLC terms for benchmarking ----------------

-- Create a term applying a builtin to one argument
mkApp1 :: (DefaultUni `Includes` a) => DefaultFun -> a -> PlainTerm
mkApp1 name x =
    erase $ mkIterApp () (builtin () name) [mkConstant () x]

-- Create a term applying a builtin to two arguments
mkApp2
    :: (DefaultUni `Includes` a, DefaultUni `Includes` b)
    =>  DefaultFun -> a -> b -> PlainTerm
mkApp2 name x y =
    erase $ mkIterApp () (builtin () name) [mkConstant () x,  mkConstant () y]

-- Create a term applying a builtin to three arguments
mkApp3
    :: (DefaultUni `Includes` a, DefaultUni `Includes` b, DefaultUni `Includes` c)
    =>  DefaultFun -> a -> b -> c -> PlainTerm
mkApp3 name x y z =
    erase $ mkIterApp () (builtin () name) [mkConstant () x,  mkConstant () y, mkConstant () z]


---------------- Creating benchmarks ----------------

{- | The use of bgroups in the functions below will cause Criterion to give the
   benchmarks names like "AddInteger/ExMemory 11/ExMemory 5": these are saved in
   the CSV file and the 'benchData' function in 'models.R' subsequently extracts
   the names and memory figures for use as entries in the data frame used to
   generate the cost models.  Hence changing the nesting of the bgroups would
   cause trouble elsewhere.
 -}


{- | Given a builtin function f of type a * b -> _ together with lists xs::[a] and
   ys::[b] (along with their memory sizes), create a collection of benchmarks
   which run f on all pairs in {(x,y}: x in xs, y in ys}. -}
createTwoTermBuiltinBench
    :: (DefaultUni `Includes` a, DefaultUni `Includes` b)
    => DefaultFun
    -> [(a, ExMemory)]
    -> [(b, ExMemory)]
    -> Benchmark
createTwoTermBuiltinBench name xs ys =
    bgroup (show name) $ [bgroup (show xmem) [mkBM yMem x y | (y, yMem) <- ys] | (x,xmem) <- xs]
        where mkBM yMem x y = runTermBench (show yMem) $ mkApp2 name x y

{- | Given a builtin function f of type a * a -> _ together with lists xs::a and
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
    :: (DefaultUni `Includes` a)
    => DefaultFun
    -> [(a, ExMemory)]
    -> [(a, ExMemory)]
    -> Benchmark
createTwoTermBuiltinBenchElementwise name xs ys =
    bgroup (show name) $ zipWith (\(x, xmem) (y,ymem) -> bgroup (show xmem) [mkBM ymem x y]) xs ys
        where mkBM ymem x y = runTermBench (show ymem) $ mkApp2 name x y
-- TODO: throw an error if xmem != ymem?  That would suggest that the caller has
-- done something wrong.


---------------- Integer builtins ----------------

-- Generate a random n-word (ie, 64n-bit) integer
{- In principle a random 5-word integer (for example) might only occupy 4 or
   fewer words, but we're generating uniformly distributed values so the
   probability of that happening should be at most 1 in 2^64. -}
randNwords :: Integer -> StdGen -> (Integer, StdGen)
randNwords n gen = randomR (lb,ub) gen
    where lb = 2^(64*(n-1))
          ub = 2^(64*n) - 1

-- Given a list [n_1, n_2, ...] create a list [m_1, m_2, ...] where m_i is an n_i-word random integer
makeSizedIntegers :: [Integer] -> StdGen -> ([Integer], StdGen)
makeSizedIntegers [] g = ([], g)
makeSizedIntegers (n:ns) g =
    let (m,g1) = randNwords n g
        (ms,g2) = makeSizedIntegers ns g1
    in (m:ms,g2)

{- For benchmarking functions with integer arguments we provide a list of random
   integers with 1,3,5,...,31 words.  Experiments suggest that these give us good
   models of the behaviour of functions for "reasonable" inputs (which will in
   fact probably only occupy one word).  We still need to guard against denial
   of service, and we may need to impose penalties for *really* large inputs. -}
makeDefaultIntegerArgs :: StdGen -> ([Integer], StdGen)
makeDefaultIntegerArgs gen = makeSizedIntegers [1, 3..31] gen

benchTwoIntegers :: StdGen -> DefaultFun -> Benchmark
benchTwoIntegers gen builtinName =
    createTwoTermBuiltinBench builtinName inputs inputs
    where
      (numbers,_) = makeDefaultIntegerArgs gen
      inputs  = fmap (\e -> (e, memoryUsage e)) numbers

benchSameTwoIntegers :: StdGen -> DefaultFun -> Benchmark
benchSameTwoIntegers gen builtinName = createTwoTermBuiltinBenchElementwise builtinName inputs inputs'
    where
      (numbers,_) = makeDefaultIntegerArgs gen
      inputs  = fmap (\e -> (e, memoryUsage e)) numbers
      inputs' = fmap (\e -> (e, memoryUsage e)) $ clone numbers
          where clone = (fmap (\n -> (n-1) `div` 3) . fmap (\n -> 3*n+1))
    -- Let's try to make sure that the numbers aren't physically identical;
    -- hopefully this is sufficiently complicated that GHC won't be able to
    -- spot that it's the identity function.


---------------- Bytestring builtins ----------------

integerPower :: Integer -> Integer -> Integer
integerPower = (^) -- Just to avoid some type ascriptions later

seedA :: HH.Seed
seedA = HH.Seed 42 43

seedB :: HH.Seed
seedB = HH.Seed 44 45

-- TODO: we're using Hedgehog for some things and System.Random for others.  We
-- should rationalise this.  Pehaps Hedgehog is more future-proof since it can
-- produce random instances of a wide variety of types.
genSample :: HH.Seed -> HH.Gen a -> a
genSample seed gen = Prelude.maybe (Prelude.error "Couldn't create a sample") HH.treeValue $ HH.evalGen (HH.Size 1) seed gen

byteStringSizes :: [Integer]
byteStringSizes = integerPower 2 <$> [1..20::Integer]

makeSizedBytestring :: HH.Seed -> Int -> (BS.ByteString, ExMemory)
makeSizedBytestring seed e = let x = genSample seed (HH.bytes (HH.Range.singleton e)) in (x, memoryUsage x)

byteStringsToBench :: HH.Seed -> [(BS.ByteString, ExMemory)]
byteStringsToBench seed = (makeSizedBytestring seed . fromInteger) <$> byteStringSizes

benchHashOperations :: DefaultFun -> Benchmark
benchHashOperations name =
    bgroup (show name) $
        byteStringsToBench seedA <&> (\(x, xmem) -> runTermBench (show xmem) $ mkApp1 name x)

benchTwoByteStrings :: DefaultFun -> Benchmark
benchTwoByteStrings name = createTwoTermBuiltinBench name (byteStringsToBench seedA) (byteStringsToBench seedB)

-- Copy the bytestring here, because otherwise it'll be exactly the same, and the equality will short-circuit.
benchSameTwoByteStrings :: DefaultFun -> Benchmark
benchSameTwoByteStrings name = createTwoTermBuiltinBenchElementwise name (byteStringsToBench seedA)
                               ((\(bs, e) -> (BS.copy bs, e)) <$> byteStringsToBench seedA)

powersOfTwo :: [Integer]
powersOfTwo = integerPower 2 <$> [1..16]

-- Make some really big numbers for benchmarking
threeToThePower :: Integer -> (Integer, ExMemory)
threeToThePower e =
    let x = integerPower 3 e
    in  (x, memoryUsage x)

benchBytestringOperations :: DefaultFun -> Benchmark -- TODO the numbers are a bit too big here
benchBytestringOperations name = createTwoTermBuiltinBench name numbers (byteStringsToBench seedA)
    where
        numbers = threeToThePower <$> powersOfTwo


---------------- Verify signature ----------------

-- for VerifySignature, for speed purposes, it shouldn't matter if the sig / pubkey are correct
sig :: BS.ByteString
sig = "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"

pubKey :: BS.ByteString
pubKey = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"

benchVerifySignature :: Benchmark
benchVerifySignature =
    bgroup (show name) $
        bs <&> (\(x, xmem) ->
            runTermBench (show xmem) $ mkApp3 name pubKey x sig
        )
    where
        name = VerifySignature
        bs = (makeSizedBytestring seedA . fromInteger) <$> byteStringSizes


---------------- Miscellaneous ----------------

-- We may need these later.
{-
benchComparison :: [Benchmark]
benchComparison = (\n -> runTermBench ("CalibratingBench/ExMemory " <> show n) (erase $ createRecursiveTerm n)) <$> [1..20]

-- Creates a cheap builtin operation to measure the base cost of executing one.
createRecursiveTerm :: Integer -> Plain PLC.Term DefaultUni DefaultFun
createRecursiveTerm d = mkIterApp () (builtin () AddInteger)
                        [ (mkConstant () (1::Integer))
                        , if d == 0
                          then mkConstant () (1::Integer)
                          else createRecursiveTerm (d-1)
                        ]
-}

{- Creates the .csv file consumed by create-cost-model. The data in this file is
   the time taken for all the builtin operations, as measured by criterion.
   See also Note [Creation of the Cost Model]. -}

{- TODO: Some care is required here regarding the current working directory.  If
   you run this benchmark via `cabal bench` or `stack bench` (but not `cabal
   run`) then the current directory will be `plutus-core`.  If you use nix it'll
   be the current shell directory, so you'll need to run it from `plutus-core`
   (NOT `plutus`, where `default.nix` is).  See SCP-2005. -}
main :: IO ()
main = do
  gen <- System.Random.getStdGen
  let dataDir = "cost-model" </> "data"
      csvFile = dataDir </> "benching.csv"
      backupFile = dataDir </> "benching.csv.backup"
  createDirectoryIfMissing True dataDir
  csvExists <- doesFileExist csvFile
  if csvExists then renameFile csvFile backupFile else pure ()

  defaultMainWith (defaultConfig { C.csvFile = Just csvFile })
                      $ (benchTwoIntegers gen <$> [ AddInteger
                                                  , SubtractInteger
                                                  , MultiplyInteger
                                                  , DivideInteger
                                                  , ModInteger
                                                  , QuotientInteger
                                                  , RemainderInteger
                                                  ])
                      <> (benchSameTwoIntegers gen <$> [ EqInteger
                                                       , LessThanInteger
                                                       , GreaterThanInteger
                                                       , LessThanEqInteger
                                                       , GreaterThanEqInteger
                                                       ])
                      <> (benchTwoByteStrings <$> [Concatenate])
                      <> (benchBytestringOperations <$> [DropByteString, TakeByteString])
                      <> (benchHashOperations <$> [SHA2, SHA3])
                      <> (benchSameTwoByteStrings <$> [ EqByteString
                                                      , LtByteString
                                                      , GtByteString
                                                      ])
                      <> [benchVerifySignature]

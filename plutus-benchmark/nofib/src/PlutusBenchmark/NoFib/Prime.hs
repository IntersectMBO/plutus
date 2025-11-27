-- editorconfig-checker-disable-file
-- cannot fix line length in this file because of large int.
{-% Primality testing functions taken from nofib/spectral/primetest.
  Most of the literate Haskell stuff has been removed and everything's
  been put into one file for simplicity. %-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-identities #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module PlutusBenchmark.NoFib.Prime where

import Control.DeepSeq (NFData)
import Data.Char (isSpace)
import GHC.Generics

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import Prelude qualified as Haskell

import PlutusCore.Pretty qualified as PLC
import PlutusTx qualified as Tx
import PlutusTx.Builtins (divideInteger, modInteger)
import PlutusTx.List
import PlutusTx.Plugin ()
import PlutusTx.Prelude as Tx hiding (even)

---------------- Extras ----------------

even :: Integer -> Bool
even n = (n `modInteger` 2) == 0

---------------- IntLib ----------------

-- We can make a large number from a list of numbers using @makeNumber@.
-- This satisfies:
-- \[@makeNumber@ \, @b@ \, [x_0,\,x_1,\,\ldots,\,x_n]
--  = x_0.@b@^n + x_1.@b@^{n-1} + \cdots + x_n.@b@^0\]
makeNumber :: Integer -> [Integer] -> Integer
makeNumber b = foldl f 0 where f a x = a * b + x
{-# INLINEABLE makeNumber #-}

-- The (left and right) inverse of @makeNumber@ is @chop@.
chop :: Integer -> Integer -> [Integer]
chop b = chop' []
  where
    chop' a n =
      if n == 0
        then a
        else chop' (r : a) q
      where
        (q, r) = n `divMod` b
{-# INLINEABLE chop #-}

{- The following function @powerMod@ calculates @a^b `mod` m@. I suspect
   that this is the critical function in the benchmarking process, and
   given that it can be computed {\em without} a great deal of extra
   storage, it should be a candidate for being a built-in within the
   Haskell library.
-}
powerMod :: Integer -> Integer -> Integer -> Integer
powerMod a b m =
  if b == 0
    then 1
    else f a' (b - 1) a'
  where
    a' = a `modInteger` m
    f a b c =
      if b == 0
        then c
        else g a b
      where
        g a b
          | even b = g ((a * a) `modInteger` m) (b `divideInteger` 2)
          | otherwise = f a (b - 1) ((a * c) `modInteger` m)
{-# INLINEABLE powerMod #-}

{- The value $@y@=@cubeRoot x@$ is the integer cube root of @x@, {\it
   i.e.} $@y@ = \lfloor \sqrt[3]{@x@} \, \rfloor$. Given $@x@\geq 0$,
   @y@ satisfies the following conditions:
   \[\begin{array}{lll}
   @y@ &\geq & 0, \\
   @y@^3 &\geq & @x@, \mbox{ and}\\
   (@y@-1)^3 &<& @x@.
   \end{array}\]

   My implementation uses Newton's method.
-}
cubeRoot :: Integer -> Integer
cubeRoot x = until satisfy improve x
  where
    satisfy y = y * y * y >= x && y' * y' * y' < x where y' = y - 1
    improve y = (2 * y * y * y + x) `ddiv` (3 * y * y)
    ddiv a b = if (r < (b `divideInteger` 2)) then q else q + 1
      where
        (q, r) = a `divMod` b
{-# INLINEABLE cubeRoot #-}

---The $@log2@ n$ is the @Integer@ $m$ such that $m = \lfloor\log_2
-- n\rfloor$.

log2 :: Integer -> Integer
log2 = Haskell.fromIntegral . length . chop 2
{-# INLINEABLE log2 #-}

---------------- Random ----------------

data RNGstate = RNGstate Integer Integer

{-% **CAUTION**.  Many functions have to return a pair (x, newState) containing their
   actual result and an updated RNG state.  Don't use let-bindings to examine these:
   if you say `let (x,r') = complicatedFunction m n r` then `complicatedFunction`
   is evaluated when you look at x and also when you look at r', doubling the
   amount of time and memory required.  This is due to a restriction in the PlutusTx
   plugin (non-strict let-bindings): to avoid it, use `case` instead:
   `case complicatedFunction m n r of ...` %-}

initRNG :: Integer -> Integer -> RNGstate
initRNG s1 s2 =
  if 1 <= s1 && s1 <= 2147483562
    then
      if 1 <= s2 && s2 <= 2147483398
        then RNGstate s1 s2
        -- error "randomInts: Bad second seed."
        else {-Tx.trace "randomInts: Bad second seed." $-} Tx.error ()
    -- error "randomInts: Bad first seed."
    else {-Tx.trace "randomInts: Bad first seed." $-} Tx.error ()
{-# INLINEABLE initRNG #-}

-- % Make a single random integer, returning that and the updated state.  In the
-- original version this was an infinite list of random numbers, but that's not
-- a good idea in the strict world.
getRandom :: RNGstate -> (Integer, RNGstate)
getRandom (RNGstate s1 s2) =
  let
    k = s1 `divideInteger` 53668
    s1' = 40014 * (s1 - k * 53668) - k * 12211
    s1'' = if s1' < 0 then s1' + 2147483563 else s1'
    k' = s2 `divideInteger` 52774
    s2' = 40692 * (s2 - k' * 52774) - k' * 3791
    s2'' = if s2' < 0 then s2' + 2147483399 else s2'
    z = s1'' - s2''
    newState = RNGstate s1'' s2''
   in
    if z < 1
      then (z + 2147483562, newState)
      else (z, newState)
{-# INLINEABLE getRandom #-}

-- % Produce a list of n random numbers, also returning the updated RNG state.
getRandoms :: Integer -> RNGstate -> ([Integer], RNGstate)
getRandoms n r = getRandoms' n r []
  where
    getRandoms' n r acc =
      if n <= 0
        then (acc, r) -- We don't need to reverse the accumulator
        else
          let (x, r') = getRandom r
           in getRandoms' (n - 1) r' (x : acc)

---------------- Prime ----------------

-- Given a value @x@ we can test whether we have a witness to @n@'s
-- compositeness using @singleTestX@.
singleTestX :: Integer -> (Integer, Integer) -> Integer -> Bool
singleTestX n (k, q) x =
  (t == 1) || (t == (n - 1)) || witness ts
  where
    (t : ts) = iterateN k square (powerMod x q n)
    witness [] = False
    witness (t : ts) =
      if t == (n - 1)
        then True
        else
          if t == 1
            then False
            else witness ts
    square x = (x * x) `modInteger` n
{-# INLINEABLE singleTestX #-}

-- The function @singleTest@ takes an odd, positive, @Integer@ @n@ and a
-- pair of @Integer@'s derived from @n@ by the @findKQ@ function
singleTest :: Integer -> (Integer, Integer) -> RNGstate -> (Bool, RNGstate)
singleTest n kq r =
  -- Tx.trace "singleTest" $
  (singleTestX n kq (2 + x), r')
  where
    (x, r') = boundedRandom (n - 2) r
{-# INLINEABLE singleTest #-}

-- The function @findKQ@ takes an odd integer $n$ and returns the tuple
-- $(k,q)$ such that $n = q2^k+1$.
findKQ :: Integer -> (Integer, Integer)
findKQ n = f (0, (n - 1))
  where
    f (k, q) =
      if r == 0
        then f (k + 1, d)
        else (k, q)
      where
        (d, r) = q `divMod` 2
{-# INLINEABLE findKQ #-}

-- % Perform k single tests on the integer n
multiTest :: Integer -> RNGstate -> Integer -> (Bool, RNGstate)
multiTest k r n =
  {-Tx.trace "* multiTest" $-}
  -- (True, r)
  if (n <= 1 || even n)
    then (n == 2, r)
    else mTest k r
  where
    mTest k r =
      if k == 0
        then (True, r)
        else case singleTest n (findKQ n) r of
          (True, r') -> mTest (k - 1) r'
          x -> x
{-# INLINEABLE multiTest #-}

-- % Original version used `take k (iterate ...)` which doesn't terminate with strict evaluation.
iterateN :: Integer -> (a -> a) -> a -> [a]
iterateN k f x =
  if k == 0
    then []
    else x : iterateN (k - 1) f (f x)
{-# INLINEABLE iterateN #-}

-- % The @boundedRandom@ function takes a number @n@ and the state of a (pseudo-) RNG @r@
-- and returns a tuple consisting of an @Integer@ $x$ in the range $0 \leq x <
-- @n@$, and the updated RNG state.
boundedRandom :: Integer -> RNGstate -> (Integer, RNGstate)
boundedRandom n r = (makeNumber 65536 (uniform ns rs), r')
  where
    ns = chop 65536 n
    (rs, r') = getRandoms (length ns) r
{-# INLINEABLE boundedRandom #-}

-- The @uniform@ function generates a sequence of @Integer@'s such that,
-- when considered as a sequence of digits, we generate a number uniform
-- in the range @0..ns@ from the random numbers @rs@.
uniform :: [Integer] -> [Integer] -> [Integer]
uniform [n] [r] = [r `modInteger` n]
uniform (n : ns) (r : rs) =
  if t == n
    then t : uniform ns rs
    else t : map ((`modInteger` 65536) . Haskell.toInteger) rs
  where
    t = Haskell.toInteger r `modInteger` (n + 1)
{-# INLINEABLE uniform #-}

---------------- Main ----------------

data PrimeID = P5 | P8 | P10 | P20 | P30 | P40 | P50 | P60 | P100 | P150 | P200
  deriving stock (Haskell.Read, Haskell.Show)

Tx.makeLift ''PrimeID

{- Some prime numbers.  The larger ones are taken from
   https://primes.utm.edu/lists/small/small.html and
   https://primes.utm.edu/lists/small/small2.html -}

getPrime :: PrimeID -> Integer
getPrime =
  \case
    P5 -> 56123
    P8 -> 81241579
    P10 -> 9576890767
    P20 -> 40206835204840513073
    P30 -> 671998030559713968361666935769
    P40 -> 5991810554633396517767024967580894321153
    P50 -> 22953686867719691230002707821868552601124472329079
    P60 -> 511704374946917490638851104912462284144240813125071454126151
    P100 ->
      2193992993218604310884461864618001945131790925282531768679169054389241527895222169476723691605898517
    P150 ->
      533791764536500962982816454877600313815808544134584704665367971790938714376754987723404131641943766815146845004667377003395107827504566198008424339207
    P200 ->
      58021664585639791181184025950440248398226136069516938232493687505822471836536824298822733710342250697739996825938232641940670857624514103125986134050997697160127301547995788468137887651823707102007839
{-# INLINEABLE getPrime #-}

-- % Only for textual output of PLC scripts
unindent :: PLC.Doc ann -> [Haskell.String]
unindent d = map (Haskell.dropWhile isSpace) $ (Haskell.lines . Haskell.show $ d)

-- % Initialise the RNG
initState :: RNGstate
initState = initRNG 111 47
{-# INLINEABLE initState #-}

-- % Parameter for multiTest: how many rounds of the main primality test do we want to perform?
numTests :: Integer
numTests = 100
{-# INLINEABLE numTests #-}

data Result = Composite | Prime
  deriving stock (Haskell.Show, Haskell.Eq, Generic)
  deriving anyclass (NFData)

-- Haskell.Eq needed for comparing Haskell results in tests.

Tx.makeLift ''Result

-- % The @processList@ function takes a list of input numbers
-- % and produces a list of output results.
processList :: [Integer] -> RNGstate -> [Result]
processList input r =
  case input of
    [] -> []
    n : ns -> case multiTest numTests r n of
      (True, r') -> Prime : processList ns r'
      (False, r') -> Composite : processList ns r'
{-# INLINEABLE processList #-}

-- % The @testInteger@ function takes a single input number and produces a single result.
testInteger :: Integer -> RNGstate -> Result
testInteger n state =
  if fst $ multiTest numTests state n -- Discard the RNG state in the result
    then Prime
    else Composite
{-# INLINEABLE testInteger #-}

-- % Haskell entry point for testing
runPrimalityTest :: Integer -> Result
runPrimalityTest n = testInteger n initState
{-# INLINEABLE runPrimalityTest #-}

-- % Run the program on an arbitrary integer, for testing
mkPrimalityTestTerm :: Integer -> Term
mkPrimalityTestTerm n =
  compiledCodeToTerm
    $ $$(Tx.compile [||runPrimalityTest||])
    `Tx.unsafeApplyCode` Tx.liftCodeDef n

-- Run the program on one of the fixed primes listed above
runFixedPrimalityTest :: PrimeID -> Result
runFixedPrimalityTest pid = runPrimalityTest (getPrime pid)

mkPrimalityCode :: PrimeID -> Tx.CompiledCode Result
mkPrimalityCode pid =
  $$(Tx.compile [||runFixedPrimalityTest||])
    `Tx.unsafeApplyCode` Tx.liftCodeDef pid

-- % Run the program on a number known to be prime, for benchmarking
-- (primes take a long time, composite numbers generally don't).
mkPrimalityBenchTerm :: PrimeID -> Term
mkPrimalityBenchTerm pid =
  compiledCodeToTerm $ mkPrimalityCode pid

{-% Primality testing functions taken from nofib/spectral/primetest.
  Most of the literate Haskell stuff has been removed and everything's
  been put into one file for simplicity. %-}

{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-identities              #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing          #-}

module Plutus.Benchmark.Prime where

import           Data.Char                    (isSpace)
import qualified Prelude                      (Eq (..), String)

import           Language.PlutusCore          (Name (..))
import qualified Language.PlutusCore.Pretty   as PLC
import           Language.PlutusCore.Universe
import qualified Language.PlutusTx            as Tx
import           Language.PlutusTx.Builtins   (divideInteger, remainderInteger)
import           Language.PlutusTx.Prelude    as Tx hiding (divMod, even)
import           Language.UntypedPlutusCore

---------------- Extras ----------------

even :: Integer -> Bool
even n = (n `remainderInteger` 2) == 0

divMod :: Integer -> Integer -> (Integer, Integer)
divMod a b = (a `divideInteger` b, a `remainderInteger` b)

---------------- IntLib ----------------

-- We can make a large number from a list of numbers using @makeNumber@.
-- This satisfies:
-- \[@makeNumber@ \, @b@ \, [x_0,\,x_1,\,\ldots,\,x_n]
--  = x_0.@b@^n + x_1.@b@^{n-1} + \cdots + x_n.@b@^0\]
{-# INLINABLE makeNumber #-}
makeNumber :: Integer -> [Integer] -> Integer
makeNumber b = foldl f 0 where f a x = a * b + x

-- The (left and right) inverse of @makeNumber@ is @chop@.
{-# INLINABLE chop #-}
chop :: Integer -> Integer -> [Integer]
chop b = chop' []
    where chop' a n =
              if n == 0
              then a
              else chop' (r:a) q
                  where (q,r) = n `divMod` b


{- The following function @powerMod@ calculates @a^b `mod` m@. I suspect
   that this is the critical function in the benchmarking process, and
   given that it can be computed {\em without} a great deal of extra
   storage, it should be a candidate for being a built-in within the
   Haskell library.
-}
{-# INLINABLE powerMod #-}
powerMod :: Integer -> Integer -> Integer -> Integer
powerMod a b m =
    if b == 0 then 1
    else f a' (b-1) a'
        where a' = a `remainderInteger` m
              f a b c = if b == 0 then c
                        else g a b where
                             g a b | even b = g ((a*a) `remainderInteger` m) (b `divideInteger` 2)
                                   | otherwise = f a (b-1) ((a*c) `remainderInteger` m)

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
{-# INLINABLE cubeRoot #-}
cubeRoot :: Integer -> Integer
cubeRoot x = until satisfy improve x
             where satisfy y = y*y*y >= x && y'*y'*y' < x where y' = y-1
                   improve y = (2*y*y*y+x) `ddiv` (3*y*y)
                   ddiv a b  = if (r < (b `divideInteger` 2)) then q else q+1
                           where (q, r) = a `divMod` b

---The $@log2@ n$ is the @Integer@ $m$ such that $m = \lfloor\log_2
-- n\rfloor$.

{-# INLINABLE log2 #-}
log2 :: Integer -> Integer
log2 = fromIntegral . length . chop 2


---------------- Random ----------------

data RNGstate = RNGstate Integer Integer

{-% **CAUTION**.  Many functions have to return a pair (x, newState) containing their
   actual result and an updated RNG state.  Don't use let-bindings to examine these:
   if you say `let (x,r') = complicatedFunction m n r` then `complicatedFunction`
   is evaluated when you look at x and also when you look at r', doubling the
   amount of time and memory required.  This is due to a restriction in the PlutusTx
   plugin (non-strict let-bindings): to avoid it, use `case` instead:
   `case complicatedFunction m n r of ...` %-}

{-# INLINABLE initRNG #-}
initRNG :: Integer -> Integer -> RNGstate
initRNG s1 s2 =
    if 1 <= s1 && s1 <= 2147483562 then
        if 1 <= s2 && s2 <= 2147483398 then RNGstate s1 s2
        else {-Tx.trace "randomInts: Bad second seed." $-} Tx.error () -- error "randomInts: Bad second seed."
    else {-Tx.trace "randomInts: Bad first seed." $-} Tx.error () -- error "randomInts: Bad first seed."


-- % Make a single random integer, returning that and the updated state.  In the
-- original version this was an infinite list of random numbers, but that's not
-- a good idea in the strict world.
{-# INLINABLE getRandom #-}
getRandom :: RNGstate -> (Integer, RNGstate)
getRandom (RNGstate s1 s2) =
    let
        k    = s1 `divideInteger` 53668
        s1'  = 40014 * (s1 - k * 53668) - k * 12211
        s1'' = if s1' < 0 then s1' + 2147483563 else s1'
        k'   = s2 `divideInteger` 52774
        s2'  = 40692 * (s2 - k' * 52774) - k' * 3791
        s2'' = if s2' < 0 then s2' + 2147483399 else s2'
        z    = s1'' - s2''
        newState = RNGstate s1'' s2''
   in  if z < 1 then (z + 2147483562, newState)
       else (z, newState)

-- % Produce a list of n random numbers, also returning the updated RNG state.
getRandoms :: Integer -> RNGstate -> ([Integer], RNGstate)
getRandoms n r = getRandoms' n r []
    where getRandoms' n r acc =
              if n <= 0 then (acc, r)  -- We don't need to reverse the accumulator
              else let (x, r') = getRandom r
                   in getRandoms' (n-1) r' (x:acc)


---------------- Prime ----------------

-- Given a value @x@ we can test whether we have a witness to @n@'s
-- compositeness using @singleTestX@.
{-# INLINABLE singleTestX #-}
singleTestX :: Integer -> (Integer, Integer) -> Integer -> Bool
singleTestX n (k, q) x
 = (t == 1) || (t == (n-1)) || witness ts
   where (t:ts)         = iterateN k square (powerMod x q n)
         witness []     = False
         witness (t:ts) = if t == (n-1) then True
                          else if t == 1 then False
                               else witness ts
         square x       = (x*x) `remainderInteger` n

-- The function @singleTest@ takes an odd, positive, @Integer@ @n@ and a
-- pair of @Integer@'s derived from @n@ by the @findKQ@ function
{-# INLINABLE singleTest #-}
singleTest :: Integer -> (Integer, Integer) -> RNGstate -> (Bool, RNGstate)
singleTest n kq r =  -- Tx.trace "singleTest" $
    (singleTestX n kq (2+x), r')
        where (x, r') = boundedRandom (n-2) r

--The function @findKQ@ takes an odd integer $n$ and returns the tuple
-- $(k,q)$ such that $n = q2^k+1$.
{-# INLINABLE findKQ #-}
findKQ :: Integer -> (Integer, Integer)
findKQ n = f (0, (n-1))
    where f (k,q) =
              if r == 0
              then f (k+1, d)
              else (k, q)
                  where (d,r) = q `divMod` 2

-- % Perform k single tests on the integer n
{-# INLINABLE multiTest #-}
multiTest :: Integer -> RNGstate-> Integer -> (Bool, RNGstate)
multiTest k r n = {-Tx.trace "* multiTest" $-}  -- (True, r)
    if (n <= 1 || even n)
    then (n==2, r)
    else mTest k r
        where mTest k r =
                  if k == 0
                  then (True, r)
                  else case singleTest n (findKQ n) r
                       of (True, r') -> mTest (k-1) r'
                          x          -> x

-- % Original version used `take k (iterate ...)` which doesn't terminate with strict evaluation.
{-# INLINABLE iterateN #-}
iterateN :: Integer -> (a -> a) -> a -> [a]
iterateN k f x =
    if k == 0 then []
    else x : iterateN (k-1) f (f x)


-- % The @boundedRandom@ function takes a number @n@ and the state of a (pseudo-) RNG @r@
-- and returns a tuple consisting of an @Integer@ $x$ in the range $0 \leq x <
-- @n@$, and the updated RNG state.
{-# INLINABLE boundedRandom #-}
boundedRandom :: Integer -> RNGstate -> (Integer, RNGstate)
boundedRandom n r = (makeNumber 65536 (uniform ns rs), r')
              where ns        = chop 65536 n
                    (rs,r') = getRandoms (length ns) r

-- The @uniform@ function generates a sequence of @Integer@'s such that,
-- when considered as a sequence of digits, we generate a number uniform
-- in the range @0..ns@ from the random numbers @rs@.
{-# INLINABLE uniform #-}
uniform :: [Integer] -> [Integer] -> [Integer]
uniform [n]    [r]    = [r `remainderInteger` n]
uniform (n:ns) (r:rs) = if t == n then t: uniform ns rs
                                  else t: map ((`remainderInteger` 65536). toInteger) rs
                        where t  = toInteger r `remainderInteger` (n+1)


---------------- Main ----------------

{-% Various test inputs.  The Haskell version easily manages numbers up
    to 200 digits, but we can't get beyond about 70 digits on the CEK machine.
    Interestingly, memory consumption on the CK machine is essentially flat and
    the times aren't much worse (maybe 10-20% greater). %-}

data PrimeID = P5 | P8 | P10 | P20 | P30 | P40 | P50 | P60
     deriving (Read, Show)

{-# INLINABLE getPrime #-}
getPrime :: PrimeID -> Integer
getPrime =
    \case
     P5  -> 56123
     P8  -> 81241579
     P10 -> 9576890767
     P20 -> 40206835204840513073
     P30 -> 671998030559713968361666935769
     P40 -> 5991810554633396517767024967580894321153
     P50 -> 22953686867719691230002707821868552601124472329079
     P60 -> 511704374946917490638851104912462284144240813125071454126151


-- % Only for textual output of PLC scripts
unindent :: PLC.Doc ann -> [Prelude.String]
unindent d = map (dropWhile isSpace) $ (lines . show $ d)


-- % Initialise the RNG
{-# INLINABLE initState #-}
initState :: RNGstate
initState = initRNG 111 47

-- % Parameter for multiTest: how many rounds of the main primality test do we want to perform?
{-# INLINABLE numTests #-}
numTests :: Integer
numTests = 100

data Result = Composite | Prime
    deriving (Show, Prelude.Eq)
-- Prelude.Eq needed for comparing Haskell results in tests.

-- % The @processList@ function takes a list of input numbers
-- % and produces a list of output results.
{-# INLINABLE processList #-}
processList :: [Integer] -> RNGstate -> [Result]
processList input r =
    case input of
      [] -> []
      n:ns -> case multiTest numTests r n
              of (True, r')  -> Prime : processList ns r'
                 (False, r') -> Composite : processList ns r'

-- % The @testInteger@ function takes a single input number and produces a single result.
{-# INLINABLE testInteger #-}
testInteger :: Integer -> RNGstate -> Result
testInteger n state = if fst $ multiTest numTests state n -- Discard the RNG state in the result
                      then Prime
                      else Composite

-- % Haskell entry point for testing
{-# INLINABLE runPrimalityTest #-}
runPrimalityTest :: Integer -> Result
runPrimalityTest n = testInteger n initState

-- % Run the program on an arbitrary integer, for testing
mkPrimalityTestTerm :: Integer -> Term Name DefaultUni ()
mkPrimalityTestTerm n =
  let (Program _ _ code) = Tx.getPlc $
                           $$(Tx.compile [|| runPrimalityTest ||])
                           `Tx.applyCode` Tx.liftCode n
  in code


-- Run the program on one of the fixed primes listed above
runFixedPrimalityTest :: PrimeID -> Result
runFixedPrimalityTest pid = runPrimalityTest (getPrime pid)

-- % Run the program on a number known to be prime, for benchmarking
-- (primes take a long time, composite numbers generally don't).
mkPrimalityBenchTerm :: PrimeID -> Term Name DefaultUni ()
mkPrimalityBenchTerm pid =
  let (Program _ _ code) = Tx.getPlc $
        $$(Tx.compile [|| runFixedPrimalityTest ||])
        `Tx.applyCode` Tx.liftCode pid
  in code

Tx.makeLift ''PrimeID
Tx.makeLift ''Result

{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- Primality testing functions taken from nofib/spectral/primetest
-- Most of the literate Haskell stuff has been removed and everything's
-- been put into one file for simplicity.

module Plutus.Benchmark.Prime where

import           Control.Monad
import           Data.Char                    (isSpace)
import qualified Prelude                      (String)
import           System.Environment

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

{- **CAUTION**.  Many functions have to return a pair (x, newState) containing their
   actual result and an updated RNG state.  Don't use let-bindings to examine these:
   if you say `let (x,r') = complicatedFunction m n r` then `complicatedFunction`
   is evaluated when you look at x and also when you look at r', doubling the
   amount of time and memory required.  This is due to a restriction in the PlutusTx
   plugin (non-strict let-bindings): to avoid it, use `case` instead:
   `case complicatedFunction m n r of ...` -}

{-# INLINABLE initRNG #-}
initRNG :: Integer -> Integer -> RNGstate
initRNG s1 s2 =
    if 1 <= s1 && s1 <= 2147483562 then
        if 1 <= s2 && s2 <= 2147483398 then RNGstate s1 s2
        else {-Tx.trace "randomInts: Bad second seed." $-} Tx.error () -- error "randomInts: Bad second seed."
    else {-Tx.trace "randomInts: Bad first seed." $-} Tx.error () -- error "randomInts: Bad first seed."


-- Make a single random integer, returning that and the updated state.  In the
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

-- Produce a list of n random numbers, also returning the updated RNG state.
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

-- Perform k single tests on the integer n
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

-- Original version used `take k (iterate ...)` which doesn't terminate with strict evaluation.
{-# INLINABLE iterateN #-}
iterateN :: Integer -> (a -> a) -> a -> [a]
iterateN k f x =
    if k == 0 then []
    else x : iterateN (k-1) f (f x)


-- The @boundedRandom@ function takes a number @n@ and the state of a (pseudo-) RNG @r@
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

-- Various test inputs.  The Haskell version easily manages numbers up
-- to 200 digits, but we can't get beyond about 70 digits on the CEK machine.
-- Interestingly, memory consumption on the CK machine is essentially flat and
-- the times aren't much worse (maybe 10-20% greater).
input :: [Integer]
input = [115756986668303657898962467957]

data PrimeID = P10 | P20 | P30 | P40 | P50 | P60
     deriving (Read, Show)

{-# INLINABLE getPrime #-}
getPrime :: PrimeID -> Integer
getPrime =
    \case
     P10 -> 9576890767
     P20 -> 40206835204840513073
     P30 -> 671998030559713968361666935769
     P40 -> 5991810554633396517767024967580894321153
     P50 -> 22953686867719691230002707821868552601124472329079
     P60 -> 511704374946917490638851104912462284144240813125071454126151
            
{- Some large primes and the time and space required to check them.

  9576890767                                                   -- 10 digits: 2.4s,  0.9 GB
  40206835204840513073                                         -- 20 digits: 4.7s,  1.8 GB
  115756986668303657898962467957                               -- 30 digits: 7.3s,  3.3 GB
  671998030559713968361666935769                               -- 30 digits: 7.5s,  3.3 GB
  4125636888562548868221559797461449                           -- 34 digits: 7.5s,  3.2 GB
  5991810554633396517767024967580894321153                     -- 40 digits: 11s,   5.2 GB
  22953686867719691230002707821868552601124472329079           -- 50 digits: 10s,   4.6 GB
  48705091355238882778842909230056712140813460157899           -- 50 digits: 10.8s, 4.7 GB
  511704374946917490638851104912462284144240813125071454126151 -- 60 digits: 15s,   7.5 GB
  7595009151080016652449223792726748985452052945413160073645842090827711  -- 70 digits: 16s, 7.7 GB (swapping on an 8GB machine)
  40979218404449071854385509743772465043384063785613460568705289173181846900181503 -- 80 digits: process killed by OS.
  23785274372342411111117777171111111111111111711111111111111111111111111111111111111111111111111111111111111
  533791764536500962982816454877600313815808544134584704665367971790938714376754987723404131641943766815146845004667377003395107827504566198008424339207
  -- ^ 150 digits: far too big for the CEK machine, 40s and 94 MB on the CK machine.
  58021664585639791181184025950440248398226136069516938232493687505822471836536824298822733710342250697739996825938232641940670857624514103125986134050997697160127301547995788468137887651823707102007839
  -- ^ 200 digits.  55s and 97 MB on the CK machine.

  8987964267331664557 -- Composite: 61ms, 68 MB

-}
          
-- Only for textual output of PLC scripts
unindent :: PLC.Doc ann -> [Prelude.String]
unindent d = map (dropWhile isSpace) $ (lines . show $ d)


-- Parameter for multiTest: how many rounds of the main primality test do we want to perform?
{-# INLINABLE numTests #-}
numTests :: Integer
numTests = 100

-- Initialise the RNG
{-# INLINABLE initState #-}
initState :: RNGstate
initState = initRNG 111 47

type Result = Tx.Bool

composite :: Result
composite = Tx.False

probablyPrime :: Result
probablyPrime = Tx.True

-- The @processList@ function takes a list of input numbers
-- and produces a list of output results.
{-# INLINABLE processList #-}
processList :: [Integer] -> RNGstate -> [Result]
processList input r =
    case input of
      [] -> []
      n:ns -> case multiTest numTests r n
              of (True, r')  -> probablyPrime : processList ns r'
                 (False, r') -> composite : processList ns r'

-- The @process@ function takes a single input number and produces a single result.
{-# INLINABLE process #-}
process :: Integer -> RNGstate -> Integer
process n r =
    case fst $ multiTest numTests r n
    of False ->  0
       True  ->  1


mkPrimeTerm :: PrimeID -> Term Name DefaultUni ()
mkPrimeTerm pid =
  let (Program _ _ code) = Tx.getPlc $ $$(Tx.compile
        [|| \n -> process n initState ||])
        `Tx.applyCode` Tx.liftCode (getPrime pid)
  in code


                 

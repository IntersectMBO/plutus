-- This module implements the operation needed to support
-- the Integer type.
module Data.Integer.Internal(
  Integer,
  zeroI, oneI, negOneI,
  eqI, neI, cmpI, ltI, leI, gtI, geI,
  addI, subI, mulI, quotRemI,
  negateI, absI,
  andI, orI, xorI,
  shiftLI, shiftRI,
  testBitI, popCountI,
  _intToInteger,
  _integerToFloatW,
  _integerToInt,
  _wordToInteger,
  ) where
import Prelude qualified ()
--import Primitives
import Control.Error
import Data.Bits
import Data.Bool
import Data.Enum
import Data.Eq
import Data.Function
import Data.Int
import Data.Integer_Type
import Data.Integral
import Data.List
import Data.Maybe_Type
import Data.Num
import Data.Ord
import Data.Word

isZero :: Integer -> Bool
isZero (I _ ds) = null ds

instance Eq Sign where
  (==) Plus Plus   = True
  (==) Minus Minus = True
  (==) _ _         = False

-- Trim off 0s and make an Integer
sI :: Sign -> [Digit] -> Integer
sI s ds =
  -- Remove trailing 0s
  case dropWhileEnd (== (0 :: Word)) ds of
    []  -> I Plus []
    ds' -> I s    ds'

zeroD :: Digit
zeroD = 0

addI :: Integer -> Integer -> Integer
addI (I Plus  xs) (I Plus  ys)                    =  I Plus  (add xs ys)
addI (I Plus  xs) (I Minus ys) | LT <- cmpW xs ys = sI Minus (sub ys xs)
                               | True             = sI Plus  (sub xs ys)
addI (I Minus xs) (I Plus  ys) | LT <- cmpW ys xs = sI Minus (sub xs ys)
                               | True             = sI Plus  (sub ys xs)
addI (I Minus xs) (I Minus ys)                    =  I Minus (add xs ys)

negateI :: Integer -> Integer
negateI i@(I _    []) = i
negateI   (I Plus  x) = I Minus x
negateI   (I Minus x) = I Plus  x

absI :: Integer -> Integer
absI (I _ x) = I Plus x

subI :: Integer -> Integer -> Integer
subI x y = addI x (negateI y)

add :: [Digit] -> [Digit] -> [Digit]
add = add' zeroD

add' :: Digit -> [Digit] -> [Digit] -> [Digit]
add' ci (x : xs) (y : ys) = s : add' co xs ys  where (co, s) = addD ci x y
add' ci (x : xs) []       = s : add' co xs []  where (co, s) = addD ci x zeroD
add' ci []       (y : ys) = s : add' co [] ys  where (co, s) = addD ci zeroD y
add' ci []       []       = if ci == zeroD then [] else [ci]

-- Add 3 digits with carry
addD :: Digit -> Digit -> Digit -> (Digit, Digit)
addD x y z = (quotMaxD s, remMaxD s)  where s = x + y + z

-- Invariant: xs >= ys, so result is always >= 0
sub :: [Digit] -> [Digit] -> [Digit]
sub xs ys = sub' zeroD xs ys

sub' :: Digit -> [Digit] -> [Digit] -> [Digit]
sub' bi (x : xs) (y : ys) = d : sub' bo xs ys  where (bo, d) = subW bi x y
sub' bi (x : xs) []       = d : sub' bo xs []  where (bo, d) = subW bi x zeroD
sub' 0  []       []       = []
sub' _  []       _        = error "impossible: xs >= ys"

-- Subtract with borrow
subW :: Digit -> Digit -> Digit -> (Digit, Digit)
subW b x y =
  let d = maxD + x - y - b
  in (1 - quotMaxD d, remMaxD d)

cmpW :: [Digit] -> [Digit] -> Ordering
cmpW (x : xs) (y : ys) =
  case cmpW xs ys of
    EQ  -> compare x y
    res -> res
cmpW (_ : _) [] = GT
cmpW [] (_ : _) = LT
cmpW [] [] = EQ

mulI :: Integer -> Integer -> Integer
mulI (I _ []) _            = I Plus []         -- 0 * x = 0
mulI _ (I _ [])            = I Plus []         -- x * 0 = 0
mulI (I sx [x]) (I sy ys)  = I (mulSign sx sy) (mulD zeroD ys x)
mulI (I sx xs)  (I sy [y]) = I (mulSign sx sy) (mulD zeroD xs y)
mulI (I sx xs)  (I sy ys)  = I (mulSign sx sy) (mulM xs ys)

mulSign :: Sign -> Sign -> Sign
mulSign s t = if s == t then Plus else Minus

-- Multiply with a single digit, and add carry.
mulD :: Digit -> [Digit] -> Digit -> [Digit]
mulD ci [] _ = if ci == 0 then [] else [ci]
mulD ci (x:xs) y = r : mulD q xs y
  where
    xy = x * y + ci
    q = quotMaxD xy
    r = remMaxD xy

mulM :: [Digit] -> [Digit] -> [Digit]
mulM xs ys =
  let rs = map (mulD zeroD xs) ys
      ss = zipWith (++) (map (`replicate` (0 :: Word)) [0 :: Int ..]) rs
  in  foldl1 add ss

-- Signs:
--  + +  -> (+,+)
--  + -  -> (-,+)
--  - +  -> (-,-)
--  - -  -> (+,-)
quotRemI :: Integer -> Integer -> (Integer, Integer)
quotRemI _         (I _  [])  = error "Integer: division by 0" -- n / 0
quotRemI (I _  [])          _ = (I Plus [], I Plus [])         -- 0 / n
quotRemI (I sx xs) (I sy ys) | Just (y, n) <- msd ys =
  -- All but the MSD are 0.  Scale numerator accordingly and divide.
  -- Then add back (the ++) the remainder we scaled off.
  let (rs, xs') = splitAt n xs  -- xs' is the scaled number
  in case quotRemD xs' y of
    (q, r) -> qrRes sx sy (q, rs ++ r)
quotRemI (I sx xs) (I sy ys)  = qrRes sx sy (quotRemB xs ys)

msd :: [Digit] -> Maybe (Digit, Int)
msd = go 0
  where
    go _ []       = Nothing
    go n [d]      = Just (d, n)
    go n (d : ds) = if d == 0 then go (n + 1) ds else Nothing

qrRes :: Sign -> Sign -> ([Digit], [Digit]) -> (Integer, Integer)
qrRes sx sy (ds, rs) = (sI (mulSign sx sy) ds, sI sx rs)

quotI :: Integer -> Integer -> Integer
quotI x y =
  case quotRemI x y of
    (q, _) -> q

-- Divide by a single digit.
-- Does not return normalized numbers.
quotRemD :: [Digit] -> Digit -> ([Digit], [Digit])
quotRemD axs y = qr zeroD (reverse axs) []
  where
    qr ci []     res = (res, [ci])
    qr ci (x:xs) res = qr r xs (q:res)
      where
        --cx = ci `unsafeShiftL` shiftD + x
        cx = ci * maxD + x
        q = quot cx y
        r = rem cx y

-- Simple iterative long division.
quotRemB :: [Digit] -> [Digit] -> ([Digit], [Digit])
quotRemB xs ys =
  let n  = I Plus xs
      d  = I Plus ys
      a  = I Plus $ replicate (length ys - (1 :: Int)) (0 :: Word) ++ [last ys]  -- only MSD of ys
      aq = quotI n a
      ar = addI d oneI
      loop q r =
        if absI r `geI` d then
          let r' = n `subI` (q `mulI` d)
              qn = q `addI` (r' `quotI` a)
              q' = (q `addI` qn) `quotI` twoI
          in  loop q' r'
        else
          q
      q' = loop aq ar
      r = n `subI` (q' `mulI` d)
  in  if r `ltI` zeroI then
        (digits (q' `subI` oneI), digits (r `addI` d))
      else
        (digits q', digits r)

digits :: Integer -> [Digit]
digits (I _ ds) = ds

zeroI :: Integer
zeroI = I Plus []

oneI :: Integer
oneI = I Plus [1]

twoI :: Integer
twoI = I Plus [2]

tenI :: Integer
tenI = I Plus [10]

negOneI :: Integer
negOneI = I Minus [1]

--------------

eqI :: Integer -> Integer -> Bool
eqI (I sx xs) (I sy ys) = sx == sy && xs == ys

neI :: Integer -> Integer -> Bool
neI x y = not (eqI x y)

cmpI :: Integer -> Integer -> Ordering
cmpI (I Plus  xs) (I Plus  ys) = cmpW xs ys
cmpI (I Minus  _) (I Plus   _) = LT
cmpI (I Plus   _) (I Minus  _) = GT
cmpI (I Minus xs) (I Minus ys) = cmpW ys xs

ltI :: Integer -> Integer -> Bool
ltI x y =
  case cmpI x y of
    LT -> True
    _  -> False

leI :: Integer -> Integer -> Bool
leI x y =
  case cmpI x y of
    GT -> False
    _  -> True

gtI :: Integer -> Integer -> Bool
gtI x y =
  case cmpI x y of
    GT -> True
    _  -> False

geI :: Integer -> Integer -> Bool
geI x y =
  case cmpI x y of
    LT -> False
    _  -> True

---------------------------------

andI :: Integer -> Integer -> Integer
andI (I Plus  xs) (I Plus  ys) = bI Plus  (andDigits xs ys)
andI (I Plus  xs) (I Minus ys) = bI Plus  (andNotDigits (sub1 ys) xs)
andI (I Minus xs) (I Plus  ys) = bI Plus  (andNotDigits (sub1 xs) ys)
andI (I Minus xs) (I Minus ys) = bI Minus (orDigits (sub1 xs) (sub1 ys))

orI :: Integer -> Integer -> Integer
orI (I Plus  xs) (I Plus  ys) = bI Plus  (orDigits xs ys)
orI (I Plus  xs) (I Minus ys) = bI Minus (andNotDigits xs (sub1 ys))
orI (I Minus xs) (I Plus  ys) = bI Minus (andNotDigits ys (sub1 xs))
orI (I Minus xs) (I Minus ys) = bI Minus (andDigits (sub1 xs) (sub1 ys))

xorI :: Integer -> Integer -> Integer
xorI (I Plus  xs) (I Plus  ys) = bI Plus  (xorDigits xs ys)
xorI (I Plus  xs) (I Minus ys) = bI Minus (xorDigits xs (sub1 ys))
xorI (I Minus xs) (I Plus  ys) = bI Minus (xorDigits (sub1 xs) ys)
xorI (I Minus xs) (I Minus ys) = bI Plus  (xorDigits (sub1 xs) (sub1 ys))

bI :: Sign -> [Digit] -> Integer
bI Plus  ds = sI Plus  ds
bI Minus ds = sI Minus (add1 ds)

add1 :: [Digit] -> [Digit]
add1 ds = add ds [1]

sub1 :: [Digit] -> [Digit]
sub1 ds = sub ds [1]

andDigits :: [Digit] -> [Digit] -> [Digit]
andDigits (x : xs) (y : ys) = (x .&. y) : andDigits xs ys
andDigits _        _        = []

andNotDigits :: [Digit] -> [Digit] -> [Digit]
andNotDigits []       []       = []
andNotDigits []       ys       = ys
andNotDigits xs       []       = []
andNotDigits (x : xs) (y : ys) = (complement x .&. y) : andNotDigits xs ys

orDigits :: [Digit] -> [Digit] -> [Digit]
orDigits []       []       = []
orDigits []       ys       = ys
orDigits xs       []       = xs
orDigits (x : xs) (y : ys) = (x .|. y) : orDigits xs ys

xorDigits :: [Digit] -> [Digit] -> [Digit]
xorDigits []       []       = []
xorDigits []       ys       = ys
xorDigits xs       []       = xs
xorDigits (x : xs) (y : ys) = (x `xor` y) : xorDigits xs ys

shiftLD :: [Digit] -> Int -> [Digit]
shiftLD ds 0 = ds
shiftLD ds i = go 0 ds
  where
    go ci [] = if ci == 0 then [] else [ci]
    go ci (d : ds) =
      let
        x = (d `unsafeShiftL` i) .|. ci
        co = quotMaxD x
        s = remMaxD x
      in s : go co ds

shiftRD :: [Digit] -> Int -> ([Digit], Bool)
shiftRD ds 0 = (ds, False)
shiftRD ds i =
  let (rs, ds') = splitAt 1 (shiftLD ds (shiftD - i))
  in  (ds', any (/= 0) rs)

testBitI :: Integer -> Int -> Bool
testBitI (I Plus  ds) i =
  case ds !? q of
    Just d  -> testBit d r
    Nothing -> False
  where (q, r) = quotRem i shiftD
testBitI (I Minus ds) i =
  -- not (testBitI (complement (I Minus ds)) i)
  case ds !? q of
    Just d ->
      let d' = if all (== 0) (take q ds) then d - 1 else d
      in  not (testBit d' r)
    Nothing -> True
  where (q, r) = quotRem i shiftD

shiftLI :: Integer -> Int -> Integer
shiftLI (I sign ds) i
  | null ds = zeroI
  | otherwise =
    let (q, r) = quotRem i shiftD
    in  I sign (replicate q 0 ++ shiftLD ds r)

shiftRI :: Integer -> Int -> Integer
shiftRI (I sign ds) i
  | null ds = zeroI
  | otherwise =
    let
      (q, r) = quotRem i shiftD
      (rs, ds') = splitAt q ds
      (ds'', shiftedOut1s) = shiftRD ds' r
    in case sign of
         Minus | shiftedOut1s || any (/= 0) rs -> I sign (add1 ds'')
         _                                     -> I sign ds''

popCountI :: Integer -> Int
popCountI (I sign ds) =
  let count = sum (map popCount ds)
  in  case sign of
        Plus  ->  count
        Minus -> -count

---------------------------------
{-
pIntegerToInteger :: P.Integer -> Integer
pIntegerToInteger i | i >= 0        = I Plus  (f i)
                    | otherwise     = I Minus (f (negate i))
  where
    f 0 = []
    f x = fromInteger (rem x (toInteger maxD)) : f (quot x (toInteger maxD))

integerToPInteger :: Integer -> P.Integer
integerToPInteger (I s xs) =
  let r = foldr (\ d r -> r * toInteger maxD + toInteger d) 0 xs
  in  case s of
        Plus  -> r
        Minus -> negate r

instance Num Integer where
  (+) = addI
  (-) = subI
  (*) = mulI
  abs x = if x < 0 then -x else x
  signum x = if x > 0 then 1 else if x < 0 then -1 else 0
  fromInteger = pIntegerToInteger

instance Enum Integer where
  fromEnum = fromEnum . integerToPInteger
  toEnum = _intToInteger

instance Real Integer where
  toRational = toRational . toInteger

instance Integral Integer where
  quotRem = quotRemI
  toInteger = integerToPInteger

--instance Show Integer where
--  show = showInteger

instance Eq Integer where
  (==) = eqI

instance Ord Integer where
  x <  y = x `ltI` y
  x <= y = x == y || x `ltI` y
  x >  y = y `ltI` x
  x >= y = x == y || y `ltI` x

instance Arbitrary Integer where
  arbitrary = do
    ndig <- frequency
      [(5,  pure 0)
      ,(25, pure 1)
      ,(20, pure 2)
      ,(10, pure 3)
      ,(10, pure 4)
      ,(2,  pure 5)
      ,(2,  pure 6)
      ]
    digits <- vectorOf ndig (chooseInt (0, maxD - 1))
    sign <- elements [Plus, Minus]
    pure $ if null digits then I Plus [] else I sign digits

{-
newtype SmallInteger = SmallInteger Integer
  deriving Show

instance Arbitrary SmallInteger where
  arbitrary = do
    ndig <- frequency
      [(25, pure 1)
      ,(20, pure 2)
      ,(10, pure 3)
      ,(10, pure 4)
      ]
    digit <- chooseInt (1, maxD - 1)
    sign <- elements [Plus, Minus]
    pure $ SmallInteger $ I sign (replicate (ndig - 1) 0 ++ [digit])
-}
{-
sanity :: HasCallStack => Integer -> Integer
sanity (I Minus []) = undefined
sanity (I _ ds) | length ds > 1 && last ds == 0 = undefined
sanity i = i
-}

prop_roundtrip1 :: Integer -> Bool
prop_roundtrip1 i = fromInteger (toInteger i) == i

prop_negate :: Integer -> Bool
prop_negate i = toInteger (negate i) == negate (toInteger i)

prop_abs :: Integer -> Bool
prop_abs i = toInteger (abs i) == abs (toInteger i)

prop_add :: Integer -> Integer -> Bool
prop_add x y = toInteger (addI x y) == toInteger x + toInteger y

prop_sub :: Integer -> Integer -> Bool
prop_sub x y = toInteger (subI x y) == toInteger x - toInteger y

prop_mul :: Integer -> Integer -> Bool
prop_mul x y = toInteger (mulI x y) == toInteger x * toInteger y

prop_div :: Integer -> NonZero Integer -> Bool
prop_div x (NonZero y) =
  to (quotRemI x y) == toInteger x `quotRem` toInteger y
  where to (a, b) = (toInteger a, toInteger b)

prop_muldiv :: Integer -> NonZero Integer -> Bool
prop_muldiv x (NonZero y) =
  let (q, r) = quotRemI x y
  in  q*y + r == x

prop_eq :: Integer -> Integer -> Bool
prop_eq x y = (eqI x y) == (toInteger x == toInteger y)

prop_ne :: Integer -> Integer -> Bool
prop_ne x y = (neI x y) == (toInteger x /= toInteger y)

prop_lt :: Integer -> Integer -> Bool
prop_lt x y = (ltI x y) == (toInteger x < toInteger y)

prop_gt :: Integer -> Integer -> Bool
prop_gt x y = (gtI x y) == (toInteger x > toInteger y)

prop_le :: Integer -> Integer -> Bool
prop_le x y = (leI x y) == (toInteger x <= toInteger y)

prop_ge :: Integer -> Integer -> Bool
prop_ge x y = (geI x y) == (toInteger x >= toInteger y)

prop_show :: Integer -> Bool
prop_show x = showInteger x == show (toInteger x)

checkAll :: IO ()
checkAll = do
  let qc p = quickCheck (withMaxSuccess 100000 p)
  mapM_ qc [prop_roundtrip1, prop_negate, prop_abs, prop_show]
  mapM_ qc [prop_add, prop_sub, prop_mul,
            prop_eq, prop_ne, prop_lt, prop_gt, prop_le, prop_ge]
  mapM_ qc [prop_div, prop_muldiv]

-}

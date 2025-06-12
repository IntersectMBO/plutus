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
import qualified Prelude()
import Primitives
import Mhs.Builtin
import Data.Bool
import Data.Function
import Data.Ord
--import Foreign.Ptr(Ptr)
--import Foreign.ForeignPtr(withForeignPtr)
import System.IO.Internal
import System.IO.Unsafe
import Data.Integer_Type

-- We cannot import Foreign.ForeignPtr; it is circular.
withForeignPtr :: ForeignPtr a -> (Ptr a -> IO b) -> IO b
withForeignPtr fp io =
  io (primForeignPtrToPtr fp) `primBind` \ b ->
  primSeq fp (primReturn b)

-----

foreign import capi "mpz_add"         mpz_add         :: Ptr MPZ -> Ptr MPZ -> Ptr MPZ ->            IO ()
foreign import capi "mpz_sub"         mpz_sub         :: Ptr MPZ -> Ptr MPZ -> Ptr MPZ ->            IO ()
foreign import capi "mpz_mul"         mpz_mul         :: Ptr MPZ -> Ptr MPZ -> Ptr MPZ ->            IO ()
foreign import capi "mpz_neg"         mpz_neg         :: Ptr MPZ -> Ptr MPZ ->                       IO ()
foreign import capi "mpz_abs"         mpz_abs         :: Ptr MPZ -> Ptr MPZ ->                       IO ()
foreign import capi "mpz_tdiv_qr"     mpz_tdiv_qr     :: Ptr MPZ -> Ptr MPZ -> Ptr MPZ -> Ptr MPZ -> IO ()
foreign import capi "mpz_cmp"         mpz_cmp         :: Ptr MPZ -> Ptr MPZ ->                       IO Int
foreign import capi "mpz_and"         mpz_and         :: Ptr MPZ -> Ptr MPZ -> Ptr MPZ ->            IO ()
foreign import capi "mpz_ior"         mpz_ior         :: Ptr MPZ -> Ptr MPZ -> Ptr MPZ ->            IO ()
foreign import capi "mpz_xor"         mpz_xor         :: Ptr MPZ -> Ptr MPZ -> Ptr MPZ ->            IO ()
foreign import capi "mpz_mul_2exp"    mpz_mul_2exp    :: Ptr MPZ -> Ptr MPZ -> Int ->                IO ()
foreign import capi "mpz_fdiv_q_2exp" mpz_fdiv_q_2exp :: Ptr MPZ -> Ptr MPZ -> Int ->                IO ()
foreign import capi "mpz_popcount"    mpz_popcount    :: Ptr MPZ ->                                  IO Int
foreign import capi "mpz_tstbit"      mpz_tstbit      :: Ptr MPZ -> Int ->                           IO Int

binop :: (Ptr MPZ -> Ptr MPZ -> Ptr MPZ -> IO ()) -> Integer -> Integer -> Integer
binop f (I x) (I y) = unsafePerformIO $ do
  z <- newMPZ
  withForeignPtr x $ \ px ->
    withForeignPtr y $ \ py ->
      withForeignPtr z $ \ pz ->
        f pz px py
  return (I z)

unop :: (Ptr MPZ -> Ptr MPZ -> IO ()) -> Integer -> Integer
unop f (I x) = unsafePerformIO $ do
  z <- newMPZ
  withForeignPtr x $ \ px ->
    withForeignPtr z $ \ pz ->
      f pz px
  return (I z)

addI :: Integer -> Integer -> Integer
addI = binop mpz_add

subI :: Integer -> Integer -> Integer
subI = binop mpz_sub

mulI :: Integer -> Integer -> Integer
mulI = binop mpz_mul

negateI :: Integer -> Integer
negateI = unop mpz_neg

absI :: Integer -> Integer
absI = unop mpz_abs

quotRemI :: Integer -> Integer -> (Integer, Integer)
quotRemI (I x) (I y) = unsafePerformIO $ do
  q <- newMPZ
  r <- newMPZ
  withForeignPtr x $ \ px ->
    withForeignPtr y $ \ py ->
      withForeignPtr q $ \ pq ->
        withForeignPtr r $ \ pr ->
          mpz_tdiv_qr pq pr px py
  return (I q, I r)

-- XXX should do quot and rem too

zeroI :: Integer
zeroI = _intToInteger (0::Int)

oneI :: Integer
oneI = _intToInteger (1::Int)

negOneI :: Integer
negOneI = _intToInteger (primIntNeg 1)

isZero :: Integer -> Bool
isZero = eqI zeroI

cmpop :: (Int -> a) -> Integer -> Integer -> a
cmpop f (I x) (I y) = unsafePerformIO $
  withForeignPtr x $ \ px ->
    withForeignPtr y $ \ py -> do
      s <- mpz_cmp px py
      return (f s)

eqI :: Integer -> Integer -> Bool
eqI = cmpop ((0::Int) ==)

neI :: Integer -> Integer -> Bool
neI = cmpop ((0::Int) /=)

cmpI :: Integer -> Integer -> Ordering
cmpI = cmpop (\ i -> if i < (0::Int) then LT else if i > (0::Int) then GT else EQ)

ltI :: Integer -> Integer -> Bool
ltI = cmpop (< (0::Int))

leI :: Integer -> Integer -> Bool
leI = cmpop (<= (0::Int))

gtI :: Integer -> Integer -> Bool
gtI = cmpop (> (0::Int))

geI :: Integer -> Integer -> Bool
geI = cmpop (>= (0::Int))

andI :: Integer -> Integer -> Integer
andI = binop mpz_and

orI :: Integer -> Integer -> Integer
orI = binop mpz_ior

xorI :: Integer -> Integer -> Integer
xorI = binop mpz_xor

-- XXX add complement

testBitI :: Integer -> Int -> Bool
testBitI (I x) i = unsafePerformIO $
  withForeignPtr x $ \ px -> do
    r <- mpz_tstbit px i
    return (r == (1::Int))

shiftLI :: Integer -> Int -> Integer
shiftLI x i = unop (\ pz px -> mpz_mul_2exp pz px i) x

shiftRI :: Integer -> Int -> Integer
shiftRI x i = unop (\ pz px -> mpz_fdiv_q_2exp pz px i) x

popCountI :: Integer -> Int
popCountI (I x) = unsafePerformIO $ withForeignPtr x mpz_popcount

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


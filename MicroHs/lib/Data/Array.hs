module Data.Array (
    module Data.Ix,
    Array,
    array,
    listArray,
    accumArray,
    (!),
    bounds,
    indices,
    elems,
    assocs,
    (//),
    accum,
    ixmap,
  ) where
import qualified Prelude()
import Primitives(primPerformIO, primArrCopy, primArrEQ)
import Control.Error
import Control.Monad
import Data.Bool
import Data.Char
import Data.Enum
import Data.Eq
import Data.Function
import Data.Functor
import Data.Int
import Data.Ix
import Data.IOArray
import Data.List
import Data.Num
import Data.Ord
import Data.Tuple
import System.IO
import Text.Show

data Array i a
   = Array (i,i)       -- bounds
           !Int        -- = (rangeSize (l,u))
           (IOArray a) -- elements

instance Ix a => Functor (Array a) where
  fmap f a@(Array b _ _) = array b [(i, f (a ! i)) | i <- range b]

instance (Ix a, Eq b)  => Eq (Array a b) where
  (==) (Array b1 _ a1) (Array b2 _ a2) = b1 == b2 && primArrEQ a1 a2

instance (Ix a, Ord b) => Ord (Array a b) where
  compare arr1 arr2 = compare (assocs arr1) (assocs arr2)

instance (Ix a, Show a, Show b) => Show (Array a b) where
  showsPrec p a =
    showParen (p > appPrec) $
    showString "array " .
    showsPrec appPrec1 (bounds a) .
    showChar ' ' .
    showsPrec appPrec1 (assocs a)

--instance (Ix a, Read a, Read b) => Read (Array a b) where
--  readsPrec = undefined

array :: (Ix a) => (a,a) -> [(a,b)] -> Array a b
array b ies =
  let n = safeRangeSize b
  in  unsafeArray' b n [(safeIndex b n i, e) | (i, e) <- ies]

listArray  :: (Ix a) => (a,a) -> [b] -> Array a b
listArray b es =
  let n = safeRangeSize b
  in  if length es > n then error "listArray: list too long" else unsafeArray' b n (zip [0..] es)

accumArray :: (Ix a) => (b -> c -> b) -> b -> (a,a) -> [(a,c)] -> Array a b
accumArray f z b = accum f (array b [(i, z) | i <- range b])

(!) :: (Ix a) => Array a b -> a -> b
(!) (Array b n a) i = primPerformIO $ readIOArray a (safeIndex b n i)

bounds :: (Ix a) => Array a b -> (a,a)
bounds (Array b _ _) = b

indices :: (Ix a) => Array a b -> [a]
indices (Array b _ _) = range b

elems :: (Ix a) => Array a b -> [b]
elems (Array _ _ a) = primPerformIO $ elemsIOArray a

assocs :: (Ix a) => Array a b -> [(a,b)]
assocs a = zip (indices a) (elems a)

(//) :: (Ix a) => Array a b -> [(a,b)] -> Array a b
(//) (Array b n oa) ies = primPerformIO $ do
  a <- primArrCopy oa
  let adj (i, e) = writeIOArray a (safeIndex b n i) e
  mapM_ adj ies
  return $ Array b n a

accum :: (Ix a) => (b -> c -> b) -> Array a b -> [(a,c)] -> Array a b
accum f arr@(Array b n _) ies = unsafeAccum f arr [(safeIndex b n i, e) | (i, e) <- ies]

ixmap :: (Ix a, Ix b) => (a,a) -> (a -> b) -> Array b c -> Array a c
ixmap b f a = array b [(i, a ! f i) | i <- range b]

-------

unsafeAccum :: (e -> a -> e) -> Array i e -> [(Int, a)] -> Array i e
unsafeAccum f (Array b n oa) ies = primPerformIO $ do
  a <- primArrCopy oa
  let adj (i, e) = do
        x <- readIOArray a i
        let x' = f x e
        seq x' (writeIOArray a i x')
  mapM_ adj ies
  return $ Array b n a

unsafeArray' :: (i,i) -> Int -> [(Int, e)] -> Array i e
unsafeArray' b n ies = primPerformIO $ do
  a <- newIOArray n arrEleBottom
  mapM_ (uncurry (writeIOArray a)) ies
  return $ Array b n a

arrEleBottom :: a
arrEleBottom = error "(Array.!): undefined array element"

safeIndex :: Ix i => (i, i) -> Int -> i -> Int
safeIndex (l,u) n i | 0 <= i' && i' < n = i'
                    | otherwise         = badSafeIndex i' n
  where i' = index (l,u) i

badSafeIndex :: Int -> Int -> a
badSafeIndex i n = error $ ("Error in array index; "::String) ++ show i ++ (" not in range [0.."::String) ++ show n ++ (")"::String)

safeRangeSize :: Ix i => (i, i) -> Int
safeRangeSize b =
  let r = rangeSize b
  in  if r < 0 then error "Negative range size" else r

elemsIOArray :: forall a . IOArray a -> IO [a]
elemsIOArray a = do
  s <- sizeIOArray a
  mapM (readIOArray a) [0::Int .. s - 1]

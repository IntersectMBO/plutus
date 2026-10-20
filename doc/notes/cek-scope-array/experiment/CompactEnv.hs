-- EXPERIMENT ONLY: persistent, exact-length arrays; copies on extension.
{-# LANGUAGE TypeFamilies #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.ArrayEnv where

import Control.Monad.ST (runST)
import Data.Primitive.SmallArray
import Data.Word (Word64)
import GHC.Exts (IsList (..))

data RAList a = ArrayEnv {-# UNPACK #-} !Int !(SmallArray a)
  deriving stock (Show)

empty :: RAList a
empty = ArrayEnv 0 emptySmallArray
{-# INLINE empty #-}

cons :: a -> RAList a -> RAList a
cons x (ArrayEnv n old) = runST $ do
  new <- newSmallArray (n + 1) x
  copySmallArray new 0 old 0 n
  ArrayEnv (n + 1) <$> unsafeFreezeSmallArray new
{-# INLINE cons #-}

contIndexOne :: b -> (a -> b) -> RAList a -> Word64 -> b
contIndexOne z f (ArrayEnv n a) i
  | i == 0 || i > fromIntegral n = z
  | otherwise = f (indexSmallArray a (n - fromIntegral i))
{-# INLINE contIndexOne #-}

indexOne :: RAList a -> Word64 -> Maybe a
indexOne e i = contIndexOne Nothing Just e i
{-# INLINE indexOne #-}

-- Requires a FULL proof of closedness from the experiment harness.
uncheckedIndexOne :: b -> (a -> b) -> RAList a -> Word64 -> b
uncheckedIndexOne _ f (ArrayEnv n a) i =
  f (indexSmallArray a (n - fromIntegral i))
{-# INLINE uncheckedIndexOne #-}

instance IsList (RAList a) where
  type Item (RAList a) = a
  fromList = foldr cons empty
  toList (ArrayEnv n a) = [indexSmallArray a i | i <- reverse [0 .. n - 1]]

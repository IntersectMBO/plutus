module Data.ZipList(ZipList(..), getZipList) where
import Prelude

newtype ZipList a = ZipList [a]
  deriving (Eq, Ord, Show)

getZipList :: forall a . ZipList a -> [a]
getZipList (ZipList as) = as

instance Functor ZipList where
  fmap f (ZipList as) = ZipList (map f as)

instance Applicative ZipList where
  pure a = ZipList (repeat a)
  liftA2 f (ZipList xs) (ZipList ys) = ZipList (zipWith f xs ys)

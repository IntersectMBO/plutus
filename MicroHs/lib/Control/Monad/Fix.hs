module Control.Monad.Fix(
  MonadFix(..),
  fix,
  ) where
import Control.Monad
import Data.Function (fix)
import Data.Functor.Identity
import Data.List.NonEmpty (NonEmpty (..))
import Data.Monoid.Internal
import Data.Tuple

class (Monad m) => MonadFix m where
  mfix :: (a -> m a) -> m a

{-
instance MonadFix Solo where
    mfix f = let a = f (unSolo a) in a
             where unSolo (MkSolo x) = x
-}
instance MonadFix Maybe where
    mfix f = let a = f (unJust a) in a
             where unJust (Just x) = x
                   unJust Nothing  = error "mfix Maybe: Nothing"

instance MonadFix [] where
    mfix f = case fix (f . head) of
               []    -> []
               (x:_) -> x : mfix (drop 1 . f)

instance MonadFix NonEmpty where
  mfix f = case fix (f . neHead) of
             ~(x :| _) -> x :| mfix (neTail . f)
    where
      neHead ~(a :| _) = a
      neTail ~(_ :| as) = as

--instance MonadFix IO where
--    mfix = fixIO

instance MonadFix ((->) r) where
  mfix f r = let a = f a r in a

instance MonadFix Identity where
  mfix f = let a = f (runIdentity a) in a

instance MonadFix (Either e) where
    mfix f = let a = f (unRight a) in a
             where unRight (Right x) = x
                   unRight (Left  _) = error "mfix Either: Left"

{-
instance MonadFix (ST s) where
        mfix = fixST

instance MonadFix Dual where
    mfix f = Dual (fix (getDual . f))

instance MonadFix Sum where
    mfix f = Sum (fix (getSum . f))

instance MonadFix Product where
    mfix f = Product (fix (getProduct . f))

instance MonadFix First where
    mfix f = First (mfix (getFirst . f))

instance MonadFix Last where
    mfix f = Last (mfix (getLast . f))

instance MonadFix f => MonadFix (Alt f) where
    mfix f = Alt (mfix (getAlt . f))

instance MonadFix f => MonadFix (Ap f) where
    mfix f = Ap (mfix (getAp . f))

instance MonadFix Down where
    mfix f = Down (fix (getDown . f))
-}

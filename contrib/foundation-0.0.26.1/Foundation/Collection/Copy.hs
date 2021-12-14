{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}

module Foundation.Collection.Copy
    ( Copy(..)
    ) where

import           GHC.ST (runST)
import           Basement.Compat.Base ((>>=))
import           Basement.Nat
import           Basement.Types.OffsetSize
import qualified Basement.Block as BLK
import qualified Basement.UArray as UA
import qualified Basement.BoxedArray as BA
import qualified Basement.String as S

#if MIN_VERSION_base(4,9,0)
import qualified Basement.Sized.Block as BLKN
import qualified Basement.Sized.List  as LN
#endif

class Copy a where
    copy :: a -> a
instance Copy [ty] where
    copy a = a
instance UA.PrimType ty => Copy (BLK.Block ty) where
    copy blk = runST (BLK.thaw blk >>= BLK.unsafeFreeze)
instance UA.PrimType ty => Copy (UA.UArray ty) where
    copy = UA.copy
instance Copy (BA.Array ty) where
    copy = BA.copy
instance Copy S.String where
    copy = S.copy

#if MIN_VERSION_base(4,9,0)
instance Copy (LN.ListN n ty) where
    copy a = a
instance (Countable ty n, UA.PrimType ty, KnownNat n) => Copy (BLKN.BlockN n ty) where
    copy blk = runST (BLKN.thaw blk >>= BLKN.freeze)
#endif

-- |
-- Module      : Foundation.System.Entropy
-- License     : BSD-style
-- Maintainer  : Foundation
-- Stability   : stable
-- Portability : good
--
{-# LANGUAGE CPP #-}
module Foundation.System.Entropy
    ( getEntropy
    ) where


import           Basement.Compat.Base
import           Basement.Types.OffsetSize
import qualified Basement.UArray.Mutable as A
import qualified Basement.UArray as A
import           Control.Exception
import           Foreign.Ptr
import           Foundation.Numerical

import           Foundation.System.Entropy.Common
#ifdef mingw32_HOST_OS
import           Foundation.System.Entropy.Windows
#else
import           Foundation.System.Entropy.Unix
#endif

-- | Get some of the system entropy
getEntropy :: CountOf Word8 -> IO (A.UArray Word8)
getEntropy n@(CountOf x) = do
    m <- A.newPinned n
    bracket entropyOpen entropyClose $ \ctx -> A.withMutablePtr m $ loop ctx x
    A.unsafeFreeze m
  where
    loop :: EntropyCtx -> Int -> Ptr Word8 -> IO ()
    loop _   0 _ = return ()
    loop ctx i p = do
        let chSz = min entropyMaximumSize i
        r <- entropyGather ctx p chSz
        if r
            then loop ctx (i-chSz) (p `plusPtr` chSz)
            else throwIO EntropySystemMissing

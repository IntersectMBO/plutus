-- |
-- Module      : Foundation.System.Entropy.Unix
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : Good
--
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ForeignFunctionInterface #-}
module Foundation.System.Entropy.Unix
    ( EntropyCtx
    , entropyOpen
    , entropyGather
    , entropyClose
    , entropyMaximumSize
    ) where

import Foreign.Ptr
import Control.Exception as E
import Control.Monad
import System.IO
import System.IO.Unsafe (unsafePerformIO)
import Basement.Compat.Base
import Basement.Compat.C.Types
import Prelude (fromIntegral)
import Foundation.System.Entropy.Common
import Foundation.Numerical

data EntropyCtx =
      EntropyCtx Handle
    | EntropySyscall

entropyOpen :: IO EntropyCtx
entropyOpen = do
    if supportSyscall
        then return EntropySyscall
        else do
            mh <- openDev "/dev/urandom"
            case mh of
                Nothing -> E.throwIO EntropySystemMissing
                Just h  -> return $ EntropyCtx h

-- | try to fill the ptr with the amount of data required.
-- Return the number of bytes, or a negative number otherwise
entropyGather :: EntropyCtx -> Ptr Word8 -> Int -> IO Bool
entropyGather (EntropyCtx h) ptr n = gatherDevEntropy h ptr n
entropyGather EntropySyscall ptr n = (==) 0 <$> c_sysrandom_linux ptr (fromIntegral n)

entropyClose :: EntropyCtx -> IO ()
entropyClose (EntropyCtx h)  = hClose h
entropyClose EntropySyscall  = return ()

entropyMaximumSize :: Int
entropyMaximumSize = 4096

openDev :: [Char] -> IO (Maybe Handle)
openDev filepath = (Just `fmap` openAndNoBuffering) `E.catch` \(_ :: IOException) -> return Nothing
  where openAndNoBuffering = do
            h <- openBinaryFile filepath ReadMode
            hSetBuffering h NoBuffering
            return h

gatherDevEntropy :: Handle -> Ptr Word8 -> Int -> IO Bool
gatherDevEntropy h ptr sz = loop ptr sz `E.catch` failOnException
  where
    loop _ 0 = return True
    loop p n = do
        r <- hGetBufSome h p n
        if r >= 0
            then loop (p `plusPtr` r) (n - r)
            else return False
    failOnException :: E.IOException -> IO Bool
    failOnException _ = return False

supportSyscall :: Bool
supportSyscall = unsafePerformIO ((==) 0 <$> c_sysrandom_linux nullPtr 0)
{-# NOINLINE supportSyscall #-}

-- return 0 on success, !0 for failure
foreign import ccall unsafe "foundation_sysrandom_linux"
   c_sysrandom_linux :: Ptr Word8 -> CSize -> IO Int

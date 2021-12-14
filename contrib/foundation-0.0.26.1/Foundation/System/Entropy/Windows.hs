-- |
-- Module      : Foundation.System.Entropy.Windows
-- License     : BSD-style
-- Maintainer  : Foundation
-- Stability   : experimental
-- Portability : Good
--
-- some code originally from cryptonite and some from the entropy package
--   Copyright (c) Thomas DuBuisson.
--
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CPP #-}
module Foundation.System.Entropy.Windows
    ( EntropyCtx
    , entropyOpen
    , entropyGather
    , entropyClose
    , entropyMaximumSize
    ) where

import Data.Int (Int32)
import Data.Word
import Foreign.C.String (CString, withCString)
import Foreign.Ptr (Ptr, nullPtr)
import Foreign.Marshal.Alloc (alloca)
import Foreign.Marshal.Utils (toBool)
import Foreign.Storable (peek)
import System.Win32.Types (getLastError)
import Control.Exception
import Foundation.System.Entropy.Common
import Basement.Compat.Base
import qualified Prelude

newtype EntropyCtx = EntropyCtx CryptCtx

entropyOpen :: IO EntropyCtx
entropyOpen = EntropyCtx <$> cryptAcquireCtx

entropyGather :: EntropyCtx -> Ptr Word8 -> Int -> IO Bool
entropyGather (EntropyCtx ctx) ptr n = cryptGenRandom ctx ptr n

entropyClose :: EntropyCtx -> IO ()
entropyClose (EntropyCtx ctx) = cryptReleaseCtx ctx

entropyMaximumSize :: Int
entropyMaximumSize = 4096

type DWORD = Word32
type BOOL  = Int32
type BYTE  = Word8

#ifdef mingw32_HOST_OS
#ifdef x86_64_HOST_ARCH
# define WINDOWS_CCONV ccall
type CryptCtx = Word64
#else
# define WINDOWS_CCONV stdcall
type CryptCtx = Word32
#endif
#else
# error Unknown windows platform
#endif

-- Declare the required CryptoAPI imports
foreign import WINDOWS_CCONV unsafe "CryptAcquireContextA"
   c_cryptAcquireCtx :: Ptr CryptCtx -> CString -> CString -> DWORD -> DWORD -> IO BOOL
foreign import WINDOWS_CCONV unsafe "CryptGenRandom"
   c_cryptGenRandom :: CryptCtx -> DWORD -> Ptr BYTE -> IO BOOL
foreign import WINDOWS_CCONV unsafe "CryptReleaseContext"
   c_cryptReleaseCtx :: CryptCtx -> DWORD -> IO BOOL


-- Define the constants we need from WinCrypt.h
msDefProv :: [Char]
msDefProv = "Microsoft Base Cryptographic Provider v1.0"

provRSAFull :: DWORD
provRSAFull = 1

cryptVerifyContext :: DWORD
cryptVerifyContext = 0xF0000000

cryptAcquireCtx :: IO CryptCtx
cryptAcquireCtx =
    alloca $ \handlePtr ->
    withCString msDefProv $ \provName -> do
        r <- toBool `fmap` c_cryptAcquireCtx handlePtr nullPtr provName provRSAFull cryptVerifyContext
        if r
            then peek handlePtr
            else throwIO EntropySystemMissing

cryptGenRandom :: CryptCtx -> Ptr Word8 -> Int -> IO Bool
cryptGenRandom h buf n = toBool `fmap` c_cryptGenRandom h (Prelude.fromIntegral n) buf


newtype WindowsRandomBackendError = WindowsRandomBackendError [Char]
    deriving (Show,Eq)

instance Exception WindowsRandomBackendError

cryptReleaseCtx :: CryptCtx -> IO ()
cryptReleaseCtx h = do
    success <- toBool `fmap` c_cryptReleaseCtx h 0
    if success
        then return ()
        else do
            lastError <- getLastError
            throwIO (WindowsRandomBackendError $ show lastError)

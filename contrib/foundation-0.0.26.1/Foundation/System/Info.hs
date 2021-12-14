-- |
-- Module      : Foundation.System.Info
-- License     : BSD-style
-- Maintainer  : foundation
-- Stability   : experimental
-- Portability : portable
--

{-# LANGUAGE CPP #-}

module Foundation.System.Info
    (
      -- * Operation System info
      OS(..)
    , os
      -- * CPU info
    , Arch(..)
    , arch
    , cpus
    , Endianness(..)
    , endianness
      -- * Compiler info
    , compilerName
    , System.Info.compilerVersion
    , Data.Version.Version(..)
    ) where

import qualified System.Info
import qualified Data.Version
import           Data.Data
import qualified GHC.Conc
import           Basement.Compat.Base
import           Basement.Endianness (Endianness(..), endianness)
import           Foundation.String

data OS
    = Windows
    | OSX
    | Linux
    | Android
    | BSD
  deriving (Show, Eq, Ord, Enum, Bounded, Data, Typeable)

-- | get the operating system on which the program is running.
--
-- Either return the known `OS` or a strict `String` of the OS name.
--
-- This function uses the `base`'s `System.Info.os` function.
--
os :: Either [Char] OS
os = case System.Info.os of
    "darwin"  -> Right OSX
    "mingw32" -> Right Windows
    "linux"   -> Right Linux
    "linux-android" -> Right Android
    "openbsd" -> Right BSD
    "netbsd"  -> Right BSD
    "freebsd" -> Right BSD
    str       -> Left str

-- | Enumeration of the known GHC supported architecture.
--
data Arch
    = I386
    | X86_64
    | PowerPC
    | PowerPC64
    | Sparc
    | Sparc64
    | ARM
    | ARM64
  deriving (Show, Eq, Ord, Enum, Bounded, Data, Typeable)

-- | get the machine architecture on which the program is running
--
-- Either return the known architecture or a Strict `String` of the
-- architecture name.
--
-- This function uses the `base`'s `System.Info.arch` function.
--
arch :: Either [Char] Arch
arch = case System.Info.arch of
    "i386"          -> Right I386
    "x86_64"        -> Right X86_64
    "powerpc"       -> Right PowerPC
    "powerpc64"     -> Right PowerPC64
    "powerpc64le"   -> Right PowerPC64
    "sparc"         -> Right Sparc
    "sparc64"       -> Right Sparc64
    "arm"           -> Right ARM
    "aarch64"       -> Right ARM64
    str             -> Left str

-- | get the compiler name
--
-- get the compilerName from base package but convert
-- it into a strict String
compilerName :: String
compilerName = fromList System.Info.compilerName

-- | returns the number of CPUs the machine has
cpus :: IO Int
cpus = GHC.Conc.getNumProcessors

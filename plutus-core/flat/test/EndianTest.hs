{-# LANGUAGE CPP #-}
module PlutusCore.Flat.Test.Main where

-- #include "MachDeps.h"

-- #include <HsBaseConfig.h>

-- import           System.Arch

isBigEndian :: Bool
isBigEndian =
#if defined(WORDS_BIGENDIAN)
    True
#else
    False
#endif

main = print isBigEndian

-- printInfo = do
--     print $ "BigEndian: " ++ show isBigEndian
--      print getSystemArch
--      print getSystemEndianness


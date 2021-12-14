-- |
-- Module      : Foundation.IO.FileMap
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- Note that the memory mapping is handled by the system, not at the haskell level.
-- The system can modify the content of the memory as any moment under your feet.
--
-- It also have the limitation of your system, no emulation or nice handling of all
-- those corners cases is attempted here.
--
-- for example mapping a large file (> 4G), on a 32 bits system is likely to just
-- fail or returns inconsistent result.
--
-- In doubt, use 'readFile' or other simple routine that brings
-- the content of the file in IO.
--
{-# LANGUAGE OverloadedStrings #-}
module Foundation.IO.FileMap
    ( fileMapRead
    , fileMapReadWith
    ) where

import           Control.Exception
import           Basement.Types.OffsetSize
import           Basement.Imports
import           Foundation.VFS (FilePath)
import           Basement.FinalPtr
import qualified Basement.UArray as V
import qualified Foundation.Foreign.MemoryMap as I
import qualified Prelude

getSize :: I.FileMapping -> Int
getSize fm
    | Prelude.fromIntegral (maxBound :: Int) < sz = error ("cannot map file in entirety as size overflow " <> show sz)
    | otherwise                                   = Prelude.fromIntegral sz
  where
    (FileSize sz) = I.fileMappingSize fm

-- | Map in memory the whole content of a file.
--
-- Once the array goes out of scope, the memory get (eventually) unmap
fileMapRead :: FilePath -> IO (V.UArray Word8)
fileMapRead fp = do
    fileMapping <- I.fileMapRead fp
    fptr <- I.fileMappingToFinalPtr fileMapping
    return $ V.foreignMem fptr (CountOf $ getSize fileMapping)

-- | Map in memory the whole content of a file,

-- the whole map is unmapped at the end of function after the function has been called
-- so any things that is still holding on to this memory will very likely trigger segfault
-- or other really bad behavior.
fileMapReadWith :: FilePath -> (V.UArray Word8 -> IO a) -> IO a
fileMapReadWith fp f = do
    bracket (I.fileMapRead fp) I.fileMappingUnmap $ \fm -> do
        fptr <- toFinalPtr (I.fileMappingPtr fm) (\_ -> return ())
        f (V.foreignMem fptr (CountOf $ getSize fm))

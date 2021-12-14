module Foundation.Conduit
    ( Conduit
    , ResourceT
    , ZipSink (..)
    , await
    , awaitForever
    , yield
    , yields
    , yieldOr
    , leftover
    , runConduit
    , runConduitPure
    , runConduitRes
    , fuse
    , (.|)
    , sourceFile
    , sourceHandle
    , sinkFile
    , sinkHandle
    , sinkList
    , bracketConduit
    ) where

import Foundation.Conduit.Internal
import Foundation.Collection
import Foundation.IO
import Foundation.IO.File
import Basement.Compat.Base
import Foundation.Monad.Base
import Foundation.Array
import Foundation
import System.IO (Handle)


infixr 2 .|
-- | Operator version of 'fuse'.
(.|) :: Monad m => Conduit a b m () -> Conduit b c m r -> Conduit a c m r
(.|) = fuse
{-# INLINE (.|) #-}

sourceFile :: MonadResource m => FilePath -> Conduit i (UArray Word8) m ()
sourceFile fp = bracketConduit
    (openFile fp ReadMode)
    closeFile
    sourceHandle

sourceHandle :: MonadIO m
             => Handle
             -> Conduit i (UArray Word8) m ()
sourceHandle h =
    loop
  where
    defaultChunkSize :: Int
    defaultChunkSize = (32 :: Int) * 1000 - 16
    loop = do
        arr <- liftIO (hGet h defaultChunkSize)
        if null arr
            then return ()
            else yield arr >> loop

-- | Send values downstream.
yields :: (Monad m, Foldable os, Element os ~ o) => os -> Conduit i o m ()
-- FIXME: Should be using mapM_ once that is in Foldable, see #334
yields = foldr ((>>) . yield) (return ())


sinkFile :: MonadResource m => FilePath -> Conduit (UArray Word8) i m ()
sinkFile fp = bracketConduit
    (openFile fp WriteMode)
    closeFile
    sinkHandle

sinkHandle :: MonadIO m
           => Handle
           -> Conduit (UArray Word8) o m ()
sinkHandle h =
    loop
  where
    loop = await >>= maybe
        (return ())
        (\arr -> liftIO (hPut h arr) >> loop)

sinkList :: Monad m => Conduit i o m [i]
sinkList =
    loop id
  where
    loop front = await >>= maybe
        (return (front []))
        (\x -> loop (front . (x:)))

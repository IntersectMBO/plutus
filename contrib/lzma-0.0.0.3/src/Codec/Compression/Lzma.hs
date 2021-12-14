{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}

-- |
-- Module      : Codec.Compression.Lzma
-- Copyright   : © 2015 Herbert Valerio Riedel
-- License     : BSD3
--
-- Maintainer  : hvr@gnu.org
-- Stability   : experimental
--
-- Compression and decompression of data streams in the lzma/xz format
--
-- See also the XZ Utils home page: <http://tukaani.org/xz/>
module Codec.Compression.Lzma
    ( -- * Simple (de)compression
      compress
    , decompress

      -- * Extended API with control over parameters
    , compressWith
    , decompressWith

#if 0
      -- * Monadic incremental (de)compression API
      --
      -- | See <http://hackage.haskell.org/package/zlib-0.6.1.1/docs/Codec-Compression-Zlib-Internal.html#g:2 zlib's incremental API documentation> for more information.

      -- ** Compression
    , CompressStream(..)
    , compressIO
    , compressST

      -- ** Decompression
    , DecompressStream(..)
    , decompressIO
    , decompressST
    , LzmaRet(..)
#endif

      -- * Parameters
      -- ** Compression parameters
    , defaultCompressParams

    , CompressParams
    , compressIntegrityCheck
    , compressLevel
    , compressLevelExtreme

    , IntegrityCheck(..)
    , CompressionLevel(..)

      -- ** Decompression parameters
    , defaultDecompressParams

    , DecompressParams
    , decompressTellNoCheck
    , decompressTellUnsupportedCheck
    , decompressTellAnyCheck
    , decompressConcatenated
    , decompressAutoDecoder
    , decompressMemLimit
    ) where

import           Control.Exception
import           Control.Monad
import           Control.Monad.ST              (stToIO)
import           Control.Monad.ST.Lazy         (ST, runST, strictToLazyST)
import qualified Control.Monad.ST.Strict       as ST.Strict (ST)
import           Control.Monad.ST.Unsafe       (unsafeIOToST)
import           Data.ByteString               (ByteString)
import qualified Data.ByteString               as BS
import qualified Data.ByteString.Lazy          as BSL
import qualified Data.ByteString.Lazy.Internal as BSL
import           GHC.IO                        (noDuplicate)
import           LibLzma

-- | Decompress lazy 'ByteString' from the @.xz@ format
decompress :: BSL.ByteString -> BSL.ByteString
decompress = decompressWith defaultDecompressParams

-- | Like 'decompress' but with the ability to specify various decompression
-- parameters. Typical usage:
--
-- > decompressWith defaultDecompressParams { decompress... = ... }
decompressWith :: DecompressParams -> BSL.ByteString -> BSL.ByteString
decompressWith _ = id

----------------------------------------------------------------------------
----------------------------------------------------------------------------

-- | Compress lazy 'ByteString' into @.xz@ format using 'defaultCompressParams'.
compress :: BSL.ByteString -> BSL.ByteString
compress = compressWith defaultCompressParams

-- | Like 'compress' but with the ability to specify various compression
-- parameters. Typical usage:
--
-- > compressWith defaultCompressParams { compress... = ... }
compressWith :: CompressParams -> BSL.ByteString -> BSL.ByteString
compressWith _ = id

#if 0

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Type derived from 'zlib' and augmented with flushing support

data CompressStream m =
     CompressInputRequired {- flush -}  (m (CompressStream m))
                           {- supply -} (ByteString -> m (CompressStream m))
       -- ^ Compression process requires input to proceed. You can
       -- either flush the stream (first field), supply an input chunk
       -- (second field), or signal the end of input (via empty
       -- chunk).
   | CompressOutputAvailable !ByteString (m (CompressStream m)) -- ^ Output chunk available.
   | CompressStreamEnd

-- | Incremental compression in the 'IO' monad.
compressIO :: CompressParams -> IO (CompressStream IO)
compressIO parms = (stToIO $ newEncodeLzmaStream parms) >>= either throwIO go
  where
    bUFSIZ = 32752

    go :: LzmaStream -> IO (CompressStream IO)
    go ls = return inputRequired
      where
        inputRequired = CompressInputRequired goFlush (withChunk goFinish goInput)

        goInput :: ByteString -> IO (CompressStream IO)
        goInput chunk = do
            (rc, used, obuf) <- stToIO $ runLzmaStream ls chunk LzmaRun bUFSIZ

            let chunk' = BS.drop used chunk

            case rc of
                LzmaRetOK
                  | BS.null obuf -> do
                      unless (used > 0) $
                          fail "compressIO: input chunk not consumed"
                      withChunk (return inputRequired) goInput chunk'
                  | otherwise    -> return (CompressOutputAvailable obuf
                                            (withChunk (return inputRequired) goInput chunk'))

                _ -> throwIO rc

        goFlush, goFinish :: IO (CompressStream IO)
        goFlush  = goSync LzmaSyncFlush (return inputRequired)
        goFinish = goSync LzmaFinish retStreamEnd

        -- drain encoder till LzmaRetStreamEnd is reported
        goSync :: LzmaAction -> IO (CompressStream IO) -> IO (CompressStream IO)
        goSync LzmaRun _ = fail "goSync called with invalid argument"
        goSync action next = goSync'
          where
            goSync' = do
                (rc, 0, obuf) <- stToIO $ runLzmaStream ls BS.empty action bUFSIZ
                case rc of
                    LzmaRetOK
                        | BS.null obuf -> fail ("compressIO: empty output chunk during " ++ show action)
                        | otherwise    -> return (CompressOutputAvailable obuf goSync')
                    LzmaRetStreamEnd
                        | BS.null obuf -> next
                        | otherwise    -> return (CompressOutputAvailable obuf next)
                    _ -> throwIO rc

        retStreamEnd = do
            !() <- stToIO (endLzmaStream ls)
            return CompressStreamEnd

-- | Incremental compression in the lazy 'ST' monad.
compressST :: CompressParams -> ST s (CompressStream (ST s))
compressST parms = strictToLazyST (newEncodeLzmaStream parms) >>=
                   either throw go
  where
    bUFSIZ = 32752

    go ls = return inputRequired
      where
        inputRequired = CompressInputRequired goFlush (withChunk goFinish goInput)

        goInput :: ByteString -> ST s (CompressStream (ST s))
        goInput chunk = do
            (rc, used, obuf) <- strictToLazyST (noDuplicateST >>
                                                runLzmaStream ls chunk LzmaRun bUFSIZ)

            let chunk' = BS.drop used chunk

            case rc of
                LzmaRetOK
                  | BS.null obuf -> do
                      unless (used > 0) $
                          fail "compressST: input chunk not consumed"
                      withChunk (return inputRequired) goInput chunk'
                  | otherwise    -> return (CompressOutputAvailable obuf
                                            (withChunk (return inputRequired) goInput chunk'))

                _ -> throw rc

        goFlush, goFinish :: ST s (CompressStream (ST s))
        goFlush  = goSync LzmaSyncFlush (return inputRequired)
        goFinish = goSync LzmaFinish retStreamEnd

        -- drain encoder till LzmaRetStreamEnd is reported
        goSync :: LzmaAction -> ST s (CompressStream (ST s)) -> ST s (CompressStream (ST s))
        goSync LzmaRun _ = fail "compressST: goSync called with invalid argument"
        goSync action next = goSync'
          where
            goSync' = do
                (rc, 0, obuf) <- strictToLazyST (noDuplicateST >>
                                                 runLzmaStream ls BS.empty action bUFSIZ)
                case rc of
                    LzmaRetOK
                        | BS.null obuf -> fail ("compressIO: empty output chunk during " ++ show action)
                        | otherwise    -> return (CompressOutputAvailable obuf goSync')
                    LzmaRetStreamEnd
                        | BS.null obuf -> next
                        | otherwise    -> return (CompressOutputAvailable obuf next)
                    _ -> throw rc

        retStreamEnd = do
            !() <- strictToLazyST (noDuplicateST >> endLzmaStream ls)
            return CompressStreamEnd

--------------------------------------------------------------------------------

data DecompressStream m =
     DecompressInputRequired (ByteString -> m (DecompressStream m)) -- ^ Decoding process requires input to proceed. An empty 'ByteString' chunk signals end of input.
   | DecompressOutputAvailable !ByteString (m (DecompressStream m)) -- ^ Decompressed output chunk available.
   | DecompressStreamEnd ByteString -- ^ Decoded stream is finished. Any unconsumed leftovers from the input stream are returned via the 'ByteString' field
   | DecompressStreamError !LzmaRet -- TODO define subset-enum of LzmaRet

-- | Incremental decompression in the 'IO' monad.
decompressIO :: DecompressParams -> IO (DecompressStream IO)
decompressIO parms = stToIO (newDecodeLzmaStream parms) >>= either (return . DecompressStreamError) go
  where
    bUFSIZ = 32752

    go :: LzmaStream -> IO (DecompressStream IO)
    go ls = return inputRequired
      where
        inputRequired = DecompressInputRequired goInput

        goInput :: ByteString -> IO (DecompressStream IO)
        goInput chunk
          | BS.null chunk = goFinish
          | otherwise = do
            (rc, used, obuf) <- stToIO $ runLzmaStream ls chunk LzmaRun bUFSIZ

            let chunk' = BS.drop used chunk

            case rc of
                LzmaRetOK
                  | BS.null obuf -> do
                      unless (used > 0) $
                          fail "decompressIO: input chunk not consumed"
                      withChunk (return inputRequired) goInput chunk'
                  | otherwise    -> return (DecompressOutputAvailable obuf
                                            (withChunk goDrain goInput chunk'))

                LzmaRetStreamEnd
                  | BS.null obuf -> retStreamEnd chunk'
                  | otherwise    -> return (DecompressOutputAvailable obuf
                                            (retStreamEnd chunk'))

                _ -> return (DecompressStreamError rc)

        goDrain, goFinish :: IO (DecompressStream IO)
        goDrain  = goSync LzmaRun (return inputRequired)
        goFinish = goSync LzmaFinish (return $ DecompressStreamError LzmaRetOK)

        goSync :: LzmaAction -> IO (DecompressStream IO) -> IO (DecompressStream IO)
        goSync action next = goSync'
          where
            goSync' = do
                (rc, 0, obuf) <- stToIO $ runLzmaStream ls BS.empty action bUFSIZ
                case rc of
                  LzmaRetOK
                    | BS.null obuf -> next
                    | otherwise    -> return (DecompressOutputAvailable obuf goSync')

                  LzmaRetStreamEnd
                    | BS.null obuf -> eof0
                    | otherwise    -> return (DecompressOutputAvailable obuf eof0)

                  _ -> return (DecompressStreamError rc)

            eof0 = retStreamEnd BS.empty

        retStreamEnd chunk' = do
            !() <- stToIO (endLzmaStream ls)
            return (DecompressStreamEnd chunk')

-- | Incremental decompression in the lazy 'ST' monad.
decompressST :: DecompressParams -> ST s (DecompressStream (ST s))
decompressST parms = strictToLazyST (newDecodeLzmaStream parms) >>=
                     either (return . DecompressStreamError) go
  where
    bUFSIZ = 32752

    go :: LzmaStream -> ST s (DecompressStream (ST s))
    go ls = return inputRequired
      where
        inputRequired = DecompressInputRequired goInput

        goInput :: ByteString -> ST s (DecompressStream (ST s))
        goInput chunk
          | BS.null chunk = goFinish
          | otherwise = do
            (rc, used, obuf) <- strictToLazyST (noDuplicateST >>
                                                runLzmaStream ls chunk LzmaRun bUFSIZ)

            let chunk' = BS.drop used chunk

            case rc of
                LzmaRetOK
                  | BS.null obuf -> do
                      unless (used > 0) $
                          fail "decompressST: input chunk not consumed"
                      withChunk (return inputRequired) goInput chunk'
                  | otherwise    -> return (DecompressOutputAvailable obuf
                                            (withChunk goDrain goInput chunk'))

                LzmaRetStreamEnd
                  | BS.null obuf -> retStreamEnd chunk'
                  | otherwise    -> return (DecompressOutputAvailable obuf
                                            (retStreamEnd chunk'))

                _ -> return (DecompressStreamError rc)


        goDrain, goFinish :: ST s (DecompressStream (ST s))
        goDrain  = goSync LzmaRun (return inputRequired)
        goFinish = goSync LzmaFinish (return $ DecompressStreamError LzmaRetOK)

        goSync :: LzmaAction -> ST s (DecompressStream (ST s)) -> ST s (DecompressStream (ST s))
        goSync action next = goSync'
          where
            goSync' = do
                (rc, 0, obuf) <- strictToLazyST (noDuplicateST >>
                                                 runLzmaStream ls BS.empty action bUFSIZ)
                case rc of
                  LzmaRetOK
                    | BS.null obuf -> next
                    | otherwise    -> return (DecompressOutputAvailable obuf goSync')

                  LzmaRetStreamEnd
                    | BS.null obuf -> eof0
                    | otherwise    -> return (DecompressOutputAvailable obuf eof0)

                  _ -> return (DecompressStreamError rc)

            eof0 = retStreamEnd BS.empty

        retStreamEnd chunk' = do
            !() <- strictToLazyST (noDuplicateST >> endLzmaStream ls)
            return (DecompressStreamEnd chunk')

-- | Small 'maybe'-ish helper distinguishing between empty and
-- non-empty 'ByteString's
withChunk :: t -> (ByteString -> t) -> ByteString -> t
withChunk emptyChunk nemptyChunk chunk
  | BS.null chunk = emptyChunk
  | otherwise     = nemptyChunk chunk

-- | See <https://github.com/haskell/zlib/issues/7>
noDuplicateST :: ST.Strict.ST s ()
noDuplicateST = unsafeIOToST noDuplicate

#endif

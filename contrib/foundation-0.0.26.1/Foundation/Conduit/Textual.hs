{-# LANGUAGE OverloadedStrings #-}
module Foundation.Conduit.Textual
    ( lines
    , words
    , fromBytes
    , toBytes
    ) where

import           Basement.Imports hiding (throw)
import           Basement.UArray (UArray)
import           Foundation.String (String)
import           Foundation.Collection
import qualified Basement.String as S
import           Foundation.Conduit.Internal
import           Foundation.Monad
import           Data.Char (isSpace)

-- | Split conduit of string to its lines
--
-- This is very similar to Prelude lines except
-- it work directly on Conduit
--
-- Note that if the newline character is not ever appearing in the stream,
-- this function will keep accumulating data until OOM
--
-- TODO: make a size-limited function
lines :: Monad m => Conduit String String m ()
lines = await >>= maybe (finish []) (go False [])
  where
    mconcatRev = mconcat . reverse

    finish l = if null l then return () else yield (mconcatRev l)

    go prevCR prevs nextBuf = do
        case S.breakLine nextBuf of
            Right (line, next)
                | S.null line && prevCR -> yield (mconcatRev (line : stripCRFromHead prevs)) >> go False mempty next
                | otherwise             -> yield (mconcatRev (line : prevs)) >> go False mempty next
            Left lastCR ->
                let nextCurrent = nextBuf : prevs
                 in await >>= maybe (finish nextCurrent) (go lastCR nextCurrent)
    stripCRFromHead []     = []
    stripCRFromHead (x:xs) = S.revDrop 1 x:xs

words :: Monad m => Conduit String String m ()
words = await >>= maybe (finish []) (go [])
  where
    mconcatRev = mconcat . reverse

    finish l = if null l then return () else yield (mconcatRev l)

    go prevs nextBuf =
        case S.dropWhile isSpace next' of
            rest' 
                | null rest' ->
                    let nextCurrent = nextBuf : prevs
                     in await >>= maybe (finish nextCurrent) (go nextCurrent)
                | otherwise  -> yield (mconcatRev (line : prevs)) >> go mempty rest'
      where (line, next') = S.break isSpace nextBuf

fromBytes :: MonadThrow m => S.Encoding -> Conduit (UArray Word8) String m ()
fromBytes encoding = loop mempty
  where
    loop r = await >>= maybe (finish r) (go r)
    finish buf | null buf  = return ()
               | otherwise = case S.fromBytes encoding buf of
                                    (s, Nothing, _)  -> yield s
                                    (_, Just err, _) -> throw err
    go current nextBuf =
        case S.fromBytes encoding (current `mappend` nextBuf) of
            (s, Nothing           , r) -> yield s >> loop r
            (s, Just S.MissingByte, r) -> yield s >> loop r
            (_, Just err          , _) -> throw err

toBytes :: Monad m => S.Encoding -> Conduit String (UArray Word8) m ()
toBytes encoding = awaitForever $ \a -> pure (S.toBytes encoding a) >>= yield

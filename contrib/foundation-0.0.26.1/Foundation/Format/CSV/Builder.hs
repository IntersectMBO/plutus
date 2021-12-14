-- |
-- Module      : Foundation.Format.CSV.Builder
-- License     : BSD-style
-- Maintainer  : Foundation
-- Stability   : experimental
-- Portability : portable
--
-- Provies the support for Comma Separated Value

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module Foundation.Format.CSV.Builder
    ( -- * String Bulider
      csvStringBuilder
    , rowStringBuilder
    , fieldStringBuilder
      -- * Block Builder
    , csvBlockBuilder
    , rowBlockBuilder
    , fieldBlockBuilder
      -- * Conduit
    , rowC
    ) where

import           Basement.Imports
import           Basement.String                  (replace)
import           Foundation.Collection.Sequential (Sequential(intersperse))
import           Foundation.Conduit.Internal

import qualified Foundation.String.Builder as String
import           Basement.Block              (Block)
import qualified Basement.Block.Builder    as Block

import           GHC.ST (runST)

import           Foundation.Format.CSV.Types

-- | serialise the CSV document into a UTF8 string
csvStringBuilder :: CSV -> String.Builder
csvStringBuilder = String.unsafeStringBuilder . csvBlockBuilder

rowStringBuilder :: Row -> String.Builder
rowStringBuilder = String.unsafeStringBuilder . rowBlockBuilder

fieldStringBuilder :: Field -> String.Builder
fieldStringBuilder = String.unsafeStringBuilder . fieldBlockBuilder

-- | serialise the CSV document into a UTF8 encoded (Block Word8)
csvBlockBuilder :: CSV -> Block.Builder
csvBlockBuilder = mconcat . intersperse (Block.emitString "\r\n") . fmap rowBlockBuilder . toList . unCSV

rowBlockBuilder :: Row -> Block.Builder
rowBlockBuilder = mconcat . intersperse (Block.emitUTF8Char ',') . fmap fieldBlockBuilder . toList . unRow

fieldBlockBuilder :: Field -> Block.Builder
fieldBlockBuilder (FieldInteger i) = Block.emitString $ show i
fieldBlockBuilder (FieldDouble  d) = Block.emitString $ show d
fieldBlockBuilder (FieldString  s e) = case e of
    NoEscape     -> Block.emitString s
    Escape       -> Block.emitUTF8Char '"' <> Block.emitString s <> Block.emitUTF8Char '"'
    DoubleEscape -> Block.emitUTF8Char '"' <> Block.emitString (replace "\"" "\"\"" s) <> Block.emitUTF8Char '"'

rowC :: (Record row, Monad m) => Conduit row (Block Word8) m ()
rowC = await >>= go
  where
    go Nothing  = pure ()
    go (Just r) =
      let bytes = runST (Block.run $ rowBlockBuilder (toRow r) <> Block.emitString "\r\n")
         in yield bytes >> await >>= go

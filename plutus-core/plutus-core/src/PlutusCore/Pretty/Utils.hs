{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Pretty.Utils
  ( prettyBytes
  ) where

import PlutusPrelude

import Data.ByteString qualified as BS
import Data.Text qualified as T
import Numeric (showHex)
import Prettyprinter.Internal

asBytes :: Word8 -> Doc ann
asBytes x = Text 2 $ T.pack $ addLeadingZero $ showHex x mempty
  where
    addLeadingZero :: String -> String
    addLeadingZero
      | x < 16 = ('0' :)
      | otherwise = id

prettyBytes :: BS.ByteString -> Doc ann
prettyBytes b = "#" <> foldMap asBytes (BS.unpack b)

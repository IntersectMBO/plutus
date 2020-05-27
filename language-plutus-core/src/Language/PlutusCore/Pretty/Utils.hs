{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Pretty.Utils
    ( prettyBytes
    , docString
    , docText
    , prettyString
    , prettyText
    ) where

import           PlutusPrelude

import qualified Data.ByteString.Lazy               as BSL
import qualified Data.Text                          as T
import           Data.Text.Prettyprint.Doc.Internal
import           Numeric                            (showHex)

asBytes :: Word8 -> Doc ann
asBytes x = Text 2 $ T.pack $ addLeadingZero $ showHex x mempty
    where addLeadingZero :: String -> String
          addLeadingZero
              | x < 16    = ('0' :)
              | otherwise = id

prettyBytes :: BSL.ByteString -> Doc ann
prettyBytes b = "#" <> fold (asBytes <$> BSL.unpack b)

{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Pretty.Utils
    ( prettyBytes
    ) where

import           PlutusPrelude

import qualified Data.ByteString        as BS
import qualified Data.Text              as T
import           Numeric                (showHex)
import           Prettyprinter.Internal

asBytes :: Word8 -> Doc ann
asBytes x = Text 2 $ T.pack $ addLeadingZero $ showHex x mempty
    where addLeadingZero :: String -> String
          addLeadingZero
              | x < 16    = ('0' :)
              | otherwise = id

prettyBytes :: BS.ByteString -> Doc ann
prettyBytes b = "#" <> fold (asBytes <$> BS.unpack b)

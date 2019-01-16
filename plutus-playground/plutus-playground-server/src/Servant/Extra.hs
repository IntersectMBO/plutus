{-# OPTIONS_GHC -Wno-orphans #-}

module Servant.Extra where

import qualified Data.ByteString.Builder  as BS
import qualified Data.ByteString.Lazy     as LBS
import           Data.Text.Encoding       (decodeUtf8With)
import           Data.Text.Encoding.Error (lenientDecode)
import           Servant                  (ToHttpApiData, toHeader, toUrlPiece)
import           Web.Cookie               (SetCookie, renderSetCookie)

-- | This is built-in in the next version of Servant. When we upgrade
-- this can be removed, along with the `no-orphans` pragma at the top of this file.
instance ToHttpApiData SetCookie where
  toUrlPiece = decodeUtf8With lenientDecode . toHeader
  toHeader = LBS.toStrict . BS.toLazyByteString . renderSetCookie

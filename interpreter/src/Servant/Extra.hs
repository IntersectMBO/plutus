{-# LANGUAGE CPP           #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Servant.Extra where

import           Data.Bifunctor           (Bifunctor, bimap)
import qualified Data.ByteString.Builder  as BS
import qualified Data.ByteString.Lazy     as LBS
import           Data.Text.Encoding       (decodeUtf8With)
import           Data.Text.Encoding.Error (lenientDecode)
import           Servant                  ((:<|>) ((:<|>)), ToHttpApiData, toHeader, toUrlPiece)
import           Web.Cookie               (SetCookie, renderSetCookie)

#if MIN_VERSION_servant(0,15,0)
#else
-- | This is built-in in the next version of Servant. When we upgrade
-- this can be removed, along with the `no-orphans` pragma at the top of this file.
instance ToHttpApiData SetCookie where
  toUrlPiece = decodeUtf8With lenientDecode . toHeader
  toHeader = LBS.toStrict . BS.toLazyByteString . renderSetCookie

-- | This is built-in in the next version of Servant. When we upgrade
-- this can be removed, along with the `no-orphans` pragma at the top of this file.
--
instance Bifunctor (:<|>) where
  bimap f g (a :<|> b) = f a :<|> g b
#endif

left ::
     (a
      :<|> b)
  -> a
left x =
  let (a :<|> _) = x
   in a

right ::
     (a
      :<|> b)
  -> b
right x =
  let (_ :<|> b) = x
   in b

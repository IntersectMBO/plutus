{-# LANGUAGE CPP #-}

-- | Flat instances for the text library
module PlutusCore.Flat.Instances.Text(
  UTF8Text(..)
#if! defined (ETA_VERSION) && ! defined (ETA)
  ,UTF16Text(..)
#endif
) where

import Data.Text qualified as T
import Data.Text.Lazy qualified as TL
import PlutusCore.Flat.Instances.Util

-- $setup
-- >>> import PlutusCore.Flat.Instances.Base()
-- >>> import PlutusCore.Flat.Instances.Test
-- >>> import qualified Data.Text             as T
-- >>> import qualified Data.Text.Lazy             as TL
-- >>> import Data.Word
-- >>> tt t = let (ts,_,bs) = tst t in (ts,bs)

{- |
Text (and Data.Text.Lazy) is encoded as a byte aligned array of bytes corresponding to its UTF8 encoding.

>>> tt $ T.pack ""
(True,[1,0])

>>> tt $ T.pack "aaa"
(True,[1,3,97,97,97,0])

>>> tt $ T.pack "¢¢¢"
(True,[1,6,194,162,194,162,194,162,0])

>>> tt $ T.pack "日日日"
(True,[1,9,230,151,165,230,151,165,230,151,165,0])

#ifndef ETA
>>> tt $ T.pack "𐍈𐍈𐍈"
(True,[1,12,240,144,141,136,240,144,141,136,240,144,141,136,0])
#endif

Strict and Lazy Text have the same encoding:

>>> tst (T.pack "abc") == tst (TL.pack "abc")
True
-}
instance Flat T.Text where
  size = sUTF8Max
  encode = eUTF8
  decode = dUTF8

instance Flat TL.Text where
  size = sUTF8Max . TL.toStrict
  encode = eUTF8 . TL.toStrict
  decode = TL.fromStrict <$> dUTF8

{-|
The desired text encoding can be explicitly specified using the wrappers UTF8Text and UTF16Text.

The default encoding is UTF8:

>>> tst (UTF8Text $ T.pack "日日日") == tst (T.pack "日日日")
True
-}
-- |A wrapper to encode/decode Text as UTF8
newtype UTF8Text = UTF8Text {unUTF8::T.Text} deriving (Eq,Ord,Show)

instance Flat UTF8Text where
  size (UTF8Text t) = sUTF8Max t
  encode (UTF8Text t) = eUTF8 t
  decode = UTF8Text <$> dUTF8

#if ! defined (ETA_VERSION) && ! defined (ETA)
{-|
>>> tt (UTF16Text $ T.pack "aaa")
(True,[1,6,97,0,97,0,97,0,0])

>>> tt (UTF16Text $ T.pack "𐍈𐍈𐍈")
(True,[1,12,0,216,72,223,0,216,72,223,0,216,72,223,0])
-}

-- |A wrapper to encode/decode Text as UTF16
newtype UTF16Text = UTF16Text {unUTF16::T.Text} deriving (Eq,Ord,Show)

instance Flat UTF16Text where
  size (UTF16Text t) = sUTF16 t
  encode (UTF16Text t) = eUTF16 t
  decode = UTF16Text <$> dUTF16
#endif


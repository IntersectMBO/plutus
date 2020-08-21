{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.PlutusCore.Pretty.PrettyConst where

import qualified Data.ByteString.Lazy               as BSL
import           Data.Foldable                      (fold)
import qualified Data.Text                          as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import           Data.Word                          (Word8)
import           Numeric                            (showHex)

{- Note [Prettyprinting built-in constants] When we're printing PLC
   code, the prettyprinter has to render built-in constants.
   Unfortunately the instance of `Data.Text.Pretyprint.Doc.Pretty` for
   `Char` and `String` (via `Char` and `[]`) does the wrong thing if
   control characters are involved.  For example, the string
   ['a', 'b', 'c', '\n', 'x', '\t', 'y', 'z'] renders as

   abc
   x    yz

   which the PLC parser can't deal with.  However, `show` renders the
   string as "abc\nx\tyz" (including the quotes), which can be
   successfuly parsed using `read`.  This class provides a
   `prettyConst` method which should be used whenever it's necessary
   to render a built-in constant: see for example
   `Language.PlutusCore.Core.Instance.Pretty.Classic`.  The constraint
   `uni `Everywhere` PrettyConst` occurs in many places in the
   codebase to make sure that we know how to print a constant from any
   type appearing in a universe of built-in types.
-}

class PrettyConst a where
    prettyConst :: a -> Doc ann
    default prettyConst :: Show a => a -> Doc ann
    prettyConst = pretty . show

-- Special instance for bytestrings
asBytes :: Word8 -> Doc ann
asBytes x = Text 2 $ T.pack $ addLeadingZero $ showHex x mempty
    where addLeadingZero :: String -> String
          addLeadingZero
              | x < 16    = ('0' :)
              | otherwise = id

instance PrettyConst BSL.ByteString where
    prettyConst b = "#" <> fold (asBytes <$> BSL.unpack b)

-- The basic built-in types use `show` via the default instance
instance PrettyConst ()
instance PrettyConst Bool
instance PrettyConst Char
instance PrettyConst Integer
instance PrettyConst String

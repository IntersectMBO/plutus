{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Pretty.PrettyConst where

import           Language.PlutusCore.Universe

import qualified Data.ByteString                    as BS
import           Data.Foldable                      (fold)
import           Data.Proxy
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

instance PrettyConst BS.ByteString where
    prettyConst b = "#" <> fold (asBytes <$> BS.unpack b)

-- The basic built-in types use `show` via the default instance
instance PrettyConst ()
instance PrettyConst Bool
instance PrettyConst Char
instance PrettyConst Integer
instance PrettyConst String
-- ^ This instance for String quotes control characters (which is what we want)
-- but also Unicode characters (\8704 and so on).  That may not be ideal.

instance GShow uni => Pretty (TypeIn uni a) where
    pretty (TypeIn uni) = pretty $ gshow uni

-- | Special treatment for built-in constants: see the Note in Language.PlutusCore.Pretty.PrettyConst.
instance (Closed uni, uni `Everywhere` PrettyConst) => Pretty (ValueOf uni a) where
    pretty (ValueOf uni x) = bring (Proxy @PrettyConst) uni $ prettyConst x

instance GShow uni => Pretty (Some (TypeIn uni)) where
    pretty (Some s) = pretty s

-- Note that the call to `pretty` here is to the instance for `ValueOf uni a`, which calls prettyConst.
instance (Closed uni, uni `Everywhere` PrettyConst) => Pretty (Some (ValueOf uni)) where
    pretty (Some s) = pretty s

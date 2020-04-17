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

class PrettyConst a where
    prettyConst :: a -> Doc ann
    default prettyConst :: Show a => a -> Doc ann
    prettyConst = pretty . show

    parseConst :: String -> a
    default parseConst :: Read a => String -> a
    parseConst = read

asBytes :: Word8 -> Doc ann
asBytes x = Text 2 $ T.pack $ addLeadingZero $ showHex x mempty
    where addLeadingZero :: String -> String
          addLeadingZero
              | x < 16    = ('0' :)
              | otherwise = id

instance PrettyConst BSL.ByteString where
    prettyConst b = "#" <> fold (asBytes <$> BSL.unpack b)

instance PrettyConst ()
instance PrettyConst Bool
instance PrettyConst Char
instance PrettyConst Integer
instance PrettyConst String

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.PlutusCore.Pretty.PrettyConst where

import qualified Data.ByteString.Lazy               as BSL
import           Data.Foldable                      (fold)
import qualified Data.Text                          as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import           Data.Word                          (Word8)
import           Numeric                            (showHex)

class {- (Read a, Show a) => -} PrettyConst a where
    prettyConst :: a -> Doc ann
--    prettyConst = pretty . show

--    parseConst :: String -> a
--    parseConst = read

asBytes :: Word8 -> Doc ann
asBytes x = Text 2 $ T.pack $ addLeadingZero $ showHex x mempty
    where addLeadingZero :: String -> String
          addLeadingZero
              | x < 16    = ('0' :)
              | otherwise = id

instance PrettyConst BSL.ByteString where
    prettyConst b = undefined -- "#" <> fold (asBytes <$> BSL.unpack b)

{- From Universe/Default.hs:

-- | We want to pretty-print constants of built-in types in a particular way.
-- Ideally, that should mean that either we have a particular class for constants pretty-printing
-- or we use a newtype to wrap the types in, so that they can be assigned a fancy 'Pretty' instance.
-- But for now we just hardcode an instance for 'ByteString'.
instance Pretty BSL.ByteString where
    pretty = prettyBytes

-}

instance Pretty BSL.ByteString where
    pretty = undefined

instance PrettyConst () where
    prettyConst = pretty

instance PrettyConst Bool where
    prettyConst = pretty

instance PrettyConst Char where
    prettyConst = pretty

instance PrettyConst Integer where
    prettyConst = pretty

instance PrettyConst String where
    prettyConst s = pretty $ show s

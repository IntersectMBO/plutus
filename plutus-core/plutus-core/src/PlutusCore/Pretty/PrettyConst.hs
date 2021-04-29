{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Pretty.PrettyConst where

import           PlutusCore.Universe

import qualified Data.ByteString                    as BS
import           Data.Coerce
import           Data.Foldable                      (fold)
import           Data.Proxy
import qualified Data.Text                          as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Internal (Doc (Text))
import           Data.Word                          (Word8)
import           Numeric                            (showHex)
import           Text.PrettyBy
import           Text.PrettyBy.Internal             (DefaultPrettyBy (..))

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
   `PlutusCore.Core.Instance.Pretty.Classic`.  The constraint
   `uni `Everywhere` PrettyConst` occurs in many places in the
   codebase to make sure that we know how to print a constant from any
   type appearing in a universe of built-in types.
-}

data ConstConfig = ConstConfig
type instance HasPrettyDefaults ConstConfig = 'False

type PrettyConst = PrettyBy ConstConfig

-- These two can be generalized to any @config@, but that breaks some use cases of 'PrettyAny'
-- then. Perhaps we should split the functionality and have two separate @newtype@ wrappers
-- in @prettyprinter-configurable@ instead of a single 'PrettyAny'.
-- For that we'll also need to ensure that it's alright when @HasPrettyDefaults config ~ 'True@.
instance DefaultPrettyBy ConstConfig (PrettyAny a) => NonDefaultPrettyBy ConstConfig (PrettyAny a)
instance DefaultPrettyBy ConstConfig (PrettyAny a) => PrettyBy ConstConfig (PrettyAny a) where
    prettyBy     = defaultPrettyBy
    prettyListBy = defaultPrettyListBy

instance Show a => DefaultPrettyBy ConstConfig (PrettyAny a) where
    defaultPrettyBy     _ = pretty . show . unPrettyAny
    defaultPrettyListBy _ = pretty . show @[a] . coerce

prettyConst :: PrettyConst a => a -> Doc ann
prettyConst = prettyBy ConstConfig

displayConst :: forall str a. (PrettyConst a, Render str) => a -> str
displayConst = render . prettyConst

-- This instance for String quotes control characters (which is what we want)
-- but also Unicode characters (\8704 and so on).  That may not be ideal.
-- Note that the spine of a tuple is pretty-printed via 'Pretty' rathen than 'Show'
-- (there is a space after each @,@). So currently only pretty-printing of lists is Making pretty-printing of polymorphic data types
-- BLAH BLAH BLAH fix me lists also have spaces after commas
-- 'Show'-based
--
-- >>> putStrLn $ displayConst ("abc\nx\tyz∀" :: String, [((), False), ((), True)])
-- ("abc\nx\tyz\8704", [((), False), ((), True)])
-- >>> putStrLn $ show         ("abc\nx\tyz∀" :: String, [((), False), ((), True)])
-- ("abc\nx\tyz\8704",[((),False),((),True)])
-- >>> putStrLn $ displayConst ["abc" :: String, "\nx\tyz", "∀"]
-- ["abc", "\nx\tyz", "\8704"]
-- >>> import Text.Read
-- >>> readMaybe "[((), False), ((), True)]" :: Maybe [((), Bool)]
-- Just [((),False),((),True)]
deriving via PrettyAny Char    instance NonDefaultPrettyBy ConstConfig Char
deriving via PrettyAny ()      instance NonDefaultPrettyBy ConstConfig ()
deriving via PrettyAny Bool    instance NonDefaultPrettyBy ConstConfig Bool
deriving via PrettyAny Integer instance NonDefaultPrettyBy ConstConfig Integer

instance PrettyConst a => NonDefaultPrettyBy ConstConfig [a]
instance (PrettyConst a, PrettyConst b) => NonDefaultPrettyBy ConstConfig (a, b)

instance PrettyBy ConstConfig BS.ByteString where
    prettyBy _ b = "#" <> fold (asBytes <$> BS.unpack b)

-- Special instance for bytestrings
asBytes :: Word8 -> Doc ann
asBytes x = Text 2 $ T.pack $ addLeadingZero $ showHex x mempty
    where addLeadingZero :: String -> String
          addLeadingZero
              | x < 16    = ('0' :)
              | otherwise = id

instance GShow uni => Pretty (SomeTypeIn uni) where
    pretty (SomeTypeIn uni) = pretty $ gshow uni

-- | Special treatment for built-in constants: see the Note in PlutusCore.Pretty.PrettyConst.
instance (Closed uni, uni `Everywhere` PrettyConst) => Pretty (ValueOf uni a) where
    pretty (ValueOf uni x) = bring (Proxy @PrettyConst) uni $ prettyConst x

-- Note that the call to `pretty` here is to the instance for `ValueOf uni a`, which calls prettyConst.
instance (Closed uni, uni `Everywhere` PrettyConst) => Pretty (Some (ValueOf uni)) where
    pretty (Some s) = pretty s

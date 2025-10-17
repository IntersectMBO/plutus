-- editorconfig-checker-disable-file
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Pretty.PrettyConst where

import PlutusCore.Data
import PlutusCore.Pretty.Readable
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as Value

import Control.Lens hiding (List)
import Data.ByteString qualified as BS
import Data.Char qualified as Char
import Data.Coerce
import Data.List.NonEmpty
import Data.Proxy
import Data.Text qualified as T
import Data.Typeable
import Data.Vector.Strict (Vector)
import Data.Word (Word8)
import Numeric (showHex)
import Prettyprinter
import Prettyprinter.Internal (Doc (Text))
import Text.PrettyBy
import Text.PrettyBy.Internal (DefaultPrettyBy (..))
import Universe

{- Note [Prettyprinting built-in constants]
When we're printing PLC code, the prettyprinter has to render built-in constants. Unfortunately the
instance of "Data.Text.Pretyprint.Doc.Pretty" for 'Text' does the wrong thing if control characters
are involved. For example, the 'Text' "abc\nx\tyz" renders as

abc
x    yz

which the PLC parser can't deal with. However, 'show' renders the string as "abc\nx\tyz" (including
the quotes).

This module provides a 'prettyConst' method which should be used whenever it's necessary to render a
built-in constant: see for example "PlutusCore.Core.Instance.Pretty.Classic". The constraint @uni
`Everywhere` PrettyConst@ occurs in many places in the codebase to make sure that we know how to
print a constant from any type appearing in a universe of built-in types.

Setting up our own machinery for overloading pretty-printing behavior would be laborious,
but fortunately the @prettyprinter-configurable@ library already provides us with all the tools
for doing that and so we define a dummy config for pretty-printing constants, implement a bunch of
instances and derive pretty-printing behavior for non-polymorphic types (including how lists of
such types are pretty-printed) via 'Show'. However always pretty-printing the spine of, say, a list
via 'Show' while pretty-printing its contents via 'PrettyConst' is not something that can be easily
done with the present-day @prettyprinter-configurable@, so we opt for pretty-printing the spine of
a value of a compound type (list of lists, list of tuples, tuple of lists etc) via 'Pretty'.
In practice this means that we have some additional spaces printed after punctuation symbols
that 'show' alone would have omitted, for example:

>>> let whateverList = ("abc\nx\tyz∀" :: Text, [((), False), ((), True)])
>>> print $ prettyConst botRenderContext whateverList
("abc\nx\tyz\8704", [((), False), ((), True)])
>>> putStrLn $ show whateverList
("abc\nx\tyz\8704",[((),False),((),True)])

Not a big deal, since our parser isn't whitespace-sensitive.
-}

-- See Note [Prettyprinting built-in constants].
-- | The type of configs used for pretty-printing constants. Has a 'RenderContext' inside, so that
-- we don't add redundant parens to the output.
newtype ConstConfig = ConstConfig
    { unConstConfig :: RenderContext
    }
type instance HasPrettyDefaults ConstConfig = 'False

instance HasRenderContext ConstConfig where
    renderContext = coerced

type PrettyConst = PrettyBy ConstConfig

-- | The set of constraints we need to be able to print built-in types and their values.
type PrettyUni uni = (PrettyParens (SomeTypeIn uni), Closed uni, uni `Everywhere` PrettyConst)

-- | The set of constraints we need to be able to throw exceptions with things with built-in types
-- and functions in them.
type ThrowableBuiltins uni fun = (PrettyUni uni, Pretty fun, Typeable uni, Typeable fun)

-- These two can be generalized to any @config@, but that breaks some use cases of 'PrettyAny'
-- then. Perhaps we should split the functionality and have two separate @newtype@ wrappers
-- in @prettyprinter-configurable@ instead of a single 'PrettyAny'.
-- For that we'll also need to ensure that it's alright when @HasPrettyDefaults config ~ 'True@.
instance DefaultPrettyBy ConstConfig (PrettyAny a) => NonDefaultPrettyBy ConstConfig (PrettyAny a)
instance DefaultPrettyBy ConstConfig (PrettyAny a) => PrettyBy ConstConfig (PrettyAny a) where
    prettyBy     = defaultPrettyBy
    prettyListBy = defaultPrettyListBy

instance Show a => DefaultPrettyBy ConstConfig (PrettyAny a) where
    defaultPrettyBy     _ = pretty . show @a   . coerce
    defaultPrettyListBy _ = pretty . show @[a] . coerce

prettyConst :: PrettyConst a => RenderContext -> a -> Doc ann
prettyConst = prettyBy . ConstConfig

-- This instance for Text quotes control characters (which is what we want)
-- but doesn't escape Unicode characters (\8704 and so on).
instance NonDefaultPrettyBy ConstConfig T.Text where
    nonDefaultPrettyListBy conf = Prettyprinter.list . Prelude.map (nonDefaultPrettyBy conf)
    nonDefaultPrettyBy = inContextM $ \t -> pure $ pretty $ "\"" <> escape t <> "\""
        where
            escape = T.foldr' prettyChar ""
            prettyChar c acc
                | c == '"' = "\\\"" <> acc -- Not handled by 'showLitChar'
                | c == '\\' = "\\\\" <> acc -- Not handled by 'showLitChar'
                | Char.isPrint c = [c] <> acc
                | otherwise = Char.showLitChar c acc

deriving via PrettyAny ()      instance NonDefaultPrettyBy ConstConfig ()
deriving via PrettyAny Bool    instance NonDefaultPrettyBy ConstConfig Bool
deriving via PrettyAny Integer instance NonDefaultPrettyBy ConstConfig Integer

-- | For rendering values without parens, i.e. in 'botRenderContext'.
newtype NoParens a = NoParens
    { unNoParens :: a
    }

instance PrettyConst a => PrettyBy ConstConfig (NoParens a) where
    prettyBy     config = prettyBy     @_ @a (config & renderContext .~ botRenderContext) . coerce
    prettyListBy config = prettyListBy @_ @a (config & renderContext .~ botRenderContext) . coerce

instance PrettyConst a => NonDefaultPrettyBy ConstConfig [a] where
    nonDefaultPrettyBy config = defaultPrettyBy @_ @[NoParens a] config . coerce
instance PrettyConst a => NonDefaultPrettyBy ConstConfig (Vector a) where
    nonDefaultPrettyBy config = defaultPrettyBy @_ @(Vector (NoParens a)) config . coerce
instance (PrettyConst a, PrettyConst b) => NonDefaultPrettyBy ConstConfig (a, b) where
    nonDefaultPrettyBy config = defaultPrettyBy @_ @(NoParens a, NoParens b) config . coerce

-- Special instance for bytestrings
asBytes :: Word8 -> Doc ann
asBytes x = Text 2 $ T.pack $ addLeadingZero $ showHex x mempty
    where addLeadingZero :: String -> String
          addLeadingZero
              | x < 16    = ('0' :)
              | otherwise = id

toBytes :: BS.ByteString -> Doc ann
toBytes  = foldMap asBytes . BS.unpack

instance PrettyBy ConstConfig Data where
    prettyBy = inContextM $ \d0 -> iterAppDocM $ \_ prettyArg -> case d0 of
        Constr i ds ->  ("Constr" <+> prettyArg i) :| [prettyArg ds]
        Map ps      ->  "Map" :| [prettyArg ps]
        List ds     ->  "List" :| [prettyArg ds]
        I i         ->  ("I" <+> prettyArg i) :| []
        B b         ->  ("B" <+> prettyArg b) :| []

instance PrettyBy ConstConfig Value.K where
    prettyBy config = prettyBy config . Value.unK

instance PrettyBy ConstConfig Value.Quantity where
    prettyBy config = prettyBy config . Value.unQuantity

instance PrettyBy ConstConfig Value where
    prettyBy config = prettyBy config . Value.toList

instance PrettyBy ConstConfig BS.ByteString where
    prettyBy _ b = "#" <> toBytes b

instance Pretty (SomeTypeIn uni) => Pretty (SomeTypeIn (Kinded uni)) where
    pretty (SomeTypeIn (Kinded uni)) = pretty (SomeTypeIn uni)

-- See Note [Prettyprinting built-in constants].
instance (Closed uni, uni `Everywhere` PrettyConst) => PrettyBy ConstConfig (ValueOf uni a) where
    prettyBy config (ValueOf uni x) = bring (Proxy @PrettyConst) uni $ prettyBy config x

-- See Note [Prettyprinting built-in constants].
instance (Closed uni, uni `Everywhere` PrettyConst) =>
        PrettyBy ConstConfig (Some (ValueOf uni)) where
    prettyBy config (Some s) = prettyBy config s

-- See Note [Prettyprinting built-in constants].
instance (Closed uni, uni `Everywhere` PrettyConst) => Pretty (ValueOf uni a) where
    pretty = prettyConst juxtRenderContext

-- See Note [Prettyprinting built-in constants].
instance (Closed uni, uni `Everywhere` PrettyConst) => Pretty (Some (ValueOf uni)) where
    pretty = prettyConst juxtRenderContext

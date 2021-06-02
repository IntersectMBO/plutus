module Decode.Helpers where

import Prelude
import Control.Monad.Except (ExceptT(..))
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Foreign (F)

-- This is a lazy version of the Alt operator to be used in the context of decoding a Foreing
-- value into a PureScript data type.
-- The problem of using <|> from Control.Alt is that `F a` is defined as an `Except MultipleErrors a`
-- which resolves to `ExceptT MultipleErrors Indentity a`, and the Identity monad is not lazy, so when
-- we do:
-- parseAsX a <|> parseAsY a
-- the value will be parsed eagerly as X and Y before discarding one option.
-- With this helper, the parsers needs to be defined as:
-- parseAsX a <|> \_ -> parseAsY a
-- but then the parseAsY will only be invoked if the parseAsX failed.
altLazy :: forall a. F a -> (Unit -> F a) -> F a
altLazy (ExceptT (Identity (Right a))) _ = pure a

altLazy _ b = b unit

infixl 3 altLazy as <|>

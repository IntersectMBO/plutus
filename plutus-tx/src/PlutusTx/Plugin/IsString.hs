{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures   #-}

module PlutusTx.Plugin.IsString (
  Utf8Encoded (..),
  RawBytes (..),
  EncodingAction (..),
) where

import Prelude

import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import Data.String (IsString (..))
import GHC.Base qualified as Magic
import PlutusTx.Builtins (BuiltinByteString)
import PlutusTx.Builtins.HasOpaque (stringToBuiltinByteString)

{- Note [IsString instances and UTF-8 encoded string literals]

GHC Core encodes string literals in UTF-8 by default.
Plugin handles GHC Core expressions representing such literals specially:
in compile type it undoes the UTF-8 encoding when string literal is used to construct
a value of type 'BuiltinByteString' and preserves the UTF-8 encoding to construct 'BuiltinString'.

The 'EncodingAction' type helps to distinguish between these two cases.

The newtypes 'Utf8Encoded' and 'RawBytes' are used to indirectly provide IsString instances
for other newtypes that wrap 'BuiltinString' or 'BuiltinByteString' i.e. 'TokenName':
  - 'utf8Encoded "Мой Токен" :: TokenName'
  - 'rawBytes "\42\33\255" :: TokenName'

-}

data EncodingAction = UndoUtf8 | PreserveUtf8

newtype Utf8Encoded (a :: Type) = Utf8Encoded {utf8Encoded :: a}

instance (Coercible a BuiltinByteString) => IsString (Utf8Encoded a) where
  fromString = Magic.noinline (coerce . stringToBuiltinByteString)

newtype RawBytes (a :: Type) = RawBytes {rawBytes :: a}

instance (Coercible a BuiltinByteString) => IsString (RawBytes a) where
  fromString = Magic.noinline (coerce . stringToBuiltinByteString)

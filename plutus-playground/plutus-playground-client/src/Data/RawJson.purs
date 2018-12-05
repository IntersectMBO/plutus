module Data.RawJson where

import Data.Lens (Iso')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Newtype (class Newtype)

import Prelude
import Data.Generic (class Generic)

newtype RawJson = RawJson String

derive instance genericRawJson :: Generic RawJson
derive instance newtypeRawJson :: Newtype RawJson _

_RawJson :: Iso' RawJson String
_RawJson = _Newtype

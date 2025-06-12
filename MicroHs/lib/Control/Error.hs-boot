-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Control.Error(module Control.Error) where
import qualified Prelude()              -- do not import Prelude
import Data.Char_Type

error :: forall a . String -> a

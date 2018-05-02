module Language.PlutusNapkin.Type ( PlutusNapkin (..)
                                  ) where

import qualified Data.ByteString.Lazy as BSL

data PlutusNapkin = PNByteString BSL.ByteString
                  | PNInt Int
                  | PNFloat Float
                  | Let PlutusNapkin PlutusNapkin

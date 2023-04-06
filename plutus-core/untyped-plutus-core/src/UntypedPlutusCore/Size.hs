module UntypedPlutusCore.Size
    ( Size (..)
    , termSize
    , programSize
    , serialisedSize
    ) where

import PlutusCore.Size (Size (..))
import UntypedPlutusCore.Core

import Control.Lens
import Data.ByteString qualified as BS
import Data.Foldable
import Flat hiding (to)

-- | Count the number of AST nodes in a term.
termSize :: Term name uni fun ann -> Size
termSize term = fold
    [ Size 1
    , term ^. termSubterms . to termSize
    ]

-- | Count the number of AST nodes in a program.
programSize :: Program name uni fun ann -> Size
programSize (Program _ _ t) = termSize t

-- | Compute the size of the serialized form of a value.
serialisedSize :: Flat a => a -> Integer
serialisedSize = fromIntegral . BS.length . flat

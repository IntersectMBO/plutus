{-| Misc. types used in this package
-}
module Plutus.ChainIndex.Types(
    BlockId
    , Page
    ) where

import qualified Data.Aeson.Extras as JSON
import qualified Data.ByteString   as BS

-- | Block identifier (usually a hash)
newtype BlockId = BlockId { getBlockId :: BS.ByteString }
    deriving (Eq, Ord)

instance Show BlockId where
    show = show . JSON.encodeByteString . getBlockId

-- | Part of a collection
data Page a = Page { pageSize :: Int, pageNumber :: Int, totalPages :: Int, pageItems :: [a]}
    deriving (Eq, Ord, Show)

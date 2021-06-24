{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-| Misc. types used in this package
-}
module Plutus.ChainIndex.Types(
    BlockId(..)
    , Page(..)
    , PageSize(..)
    , pageOf
    , Tip(..)
    ) where

import           Data.Aeson      (FromJSON, ToJSON)
import qualified Data.ByteString as BS
import           Data.Default    (Default (..))
import           Data.Set        (Set)
import qualified Data.Set        as Set
import           GHC.Generics    (Generic)
import           Ledger.Bytes    (LedgerBytes (..))
import           Ledger.Slot     (Slot)
import           Numeric.Natural (Natural)

-- | Block identifier (usually a hash)
newtype BlockId = BlockId { getBlockId :: BS.ByteString }
    deriving stock (Eq, Ord, Generic)
    deriving (ToJSON, FromJSON,Show) via LedgerBytes

newtype PageSize = PageSize { getPageSize :: Natural }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Default PageSize where
    def = PageSize 50

-- | Part of a collection
data Page a = Page { pageSize :: PageSize, pageNumber :: Int, totalPages :: Int, pageItems :: [a]}
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | A page with the given size
pageOf :: PageSize -> Set a -> Page a
pageOf (PageSize ps) items =
    let totalPages =
            let (d, m) = Set.size items `divMod` ps'
            in if m == 0 then d else d + 1
        ps' = fromIntegral ps
    in Page
        { pageSize = PageSize ps
        , pageNumber = 1
        , totalPages
        , pageItems = take ps' $ Set.toList items
        }

-- | The tip of the chain index
data Tip =
    -- TODO: Add genesis block tip
    Tip
        { tipSlot    :: Slot -- ^ Last slot
        , tipBlockId :: BlockId -- ^ Last block ID
        , tipBlockNo :: Int -- ^ Last block number (if available)
        }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)


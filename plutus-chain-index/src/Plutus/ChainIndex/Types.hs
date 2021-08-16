{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-| Misc. types used in this package
-}
module Plutus.ChainIndex.Types(
    BlockId(..)
    , Page(..)
    , PageSize(..)
    , pageOf
    , Tip(..)
    ) where

import           Data.Aeson        (FromJSON, ToJSON)
import           Data.Default      (Default (..))
import           Data.Set          (Set)
import qualified Data.Set          as Set
import           GHC.Generics      (Generic)
import           Ledger.Blockchain (BlockId (..))
import           Ledger.Slot       (Slot)
import           Numeric.Natural   (Natural)
import           Prettyprinter     (Pretty (..), (<+>))

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

-- | The tip of the chain index.
data Tip =
      TipAtGenesis
    | Tip
        { tipSlot    :: Slot -- ^ Last slot
        , tipBlockId :: BlockId -- ^ Last block ID
        , tipBlockNo :: Int -- ^ Last block number
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | This mirrors the previously defined Tip which used the Last monoid definition.
instance Semigroup Tip where
    t <> TipAtGenesis = t
    _ <> t            = t

instance Monoid Tip where
    mempty = TipAtGenesis

instance Ord Tip where
    TipAtGenesis <= _            = True
    _            <= TipAtGenesis = False
    (Tip _ _ ln) <= (Tip _ _ rn) = ln <= rn

instance Pretty Tip where
    pretty TipAtGenesis = "TipAtGenesis"
    pretty Tip {tipSlot, tipBlockId, tipBlockNo} =
            "Tip(slot="
        <+> pretty tipSlot
        <>  ", blockId="
        <+> pretty tipBlockId
        <> ", blockNo="
        <+> pretty tipBlockNo
        <>  ")"

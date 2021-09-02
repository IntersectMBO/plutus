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
    , Point(..)
    , pointsToTip
    , tipAsPoint
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

-- | When performing a rollback the chain sync protocol does not provide a block
--   number where to resume from.
data Point =
      PointAtGenesis
    | Point
        { pointSlot    :: Slot -- ^ Slot number
        , pointBlockId :: BlockId -- ^ Block number
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Ord Point where
  PointAtGenesis <= _              = True
  _              <= PointAtGenesis = False
  (Point ls _)   <= (Point rs _)   = ls <= rs

instance Pretty Point where
    pretty PointAtGenesis = "PointAtGenesis"
    pretty Point {pointSlot, pointBlockId} =
            "Tip(slot="
        <+> pretty pointSlot
        <>  ", blockId="
        <+> pretty pointBlockId
        <>  ")"

tipAsPoint :: Tip -> Point
tipAsPoint TipAtGenesis = PointAtGenesis
tipAsPoint (Tip tSlot tBlockId _) =
    Point { pointSlot = tSlot
          , pointBlockId = tBlockId
          }

pointsToTip :: Point -> Tip -> Bool
pointsToTip PointAtGenesis TipAtGenesis = True
pointsToTip (Point pSlot pBlockId)
            (Tip   tSlot tBlockId _)
  | tSlot == pSlot && tBlockId == pBlockId = True
pointsToTip _ _ = False

-- | This mirrors the previously defined Tip which used the Last monoid definition.
instance Semigroup Tip where
    t <> TipAtGenesis = t
    _ <> t            = t

instance Monoid Tip where
    mempty = TipAtGenesis

instance Ord Tip where
    TipAtGenesis <= _            = True
    _            <= TipAtGenesis = False
    (Tip ls _ _) <= (Tip rs _ _) = ls <= rs

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

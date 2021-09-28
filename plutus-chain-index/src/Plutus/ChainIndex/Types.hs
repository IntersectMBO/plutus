{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-| Misc. types used in this package
-}
module Plutus.ChainIndex.Types(
    BlockId(..)
    , blockId
    , Page(..)
    , PageSize(..)
    , pageOf
    , Tip(..)
    , Point(..)
    , pointsToTip
    , tipAsPoint
    , TxValidity(..)
    , TxStatus(..)
    , BlockNumber(..)
    , Depth(..)
    , Diagnostics(..)
    , TxConfirmedState(..)
    , TxStatusFailure(..)
    , TxIdState(..)
    ) where

import qualified Codec.Serialise                  as CBOR
import           Crypto.Hash                      (SHA256, hash)
import           Data.Aeson                       (FromJSON, ToJSON)
import qualified Data.ByteArray                   as BA
import qualified Data.ByteString.Lazy             as BSL
import           Data.Default                     (Default (..))
import           Data.Map                         (Map)
import qualified Data.Map                         as Map
import           Data.Monoid                      (Last (..), Sum (..))
import           Data.Semigroup.Generic           (GenericSemigroupMonoid (..))
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Text.Prettyprint.Doc.Extras (PrettyShow (..))
import           Data.Word                        (Word64)
import           GHC.Generics                     (Generic)
import           Ledger.Blockchain                (Block, BlockId (..))
import           Ledger.Slot                      (Slot)
import           Ledger.TxId                      (TxId)
import           Numeric.Natural                  (Natural)
import           PlutusTx.Lattice                 (MeetSemiLattice (..))
import           Prettyprinter                    (Pretty (..), (<+>))

newtype PageSize = PageSize { getPageSize :: Natural }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Default PageSize where
    def = PageSize 50

-- | Compute a hash of the block's contents.
blockId :: Block -> BlockId
blockId = BlockId
        . BA.convert
        . hash @_ @SHA256
        . BSL.toStrict
        . CBOR.serialise
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
        , tipBlockNo :: BlockNumber -- ^ Last block number
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

-- | Validity of a transaction that has been added to the ledger
data TxValidity = TxValid | TxInvalid | UnknownValidity
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving Pretty via (PrettyShow TxValidity)

instance MeetSemiLattice TxValidity where
  TxValid /\ TxValid     = TxValid
  TxInvalid /\ TxInvalid = TxInvalid
  _ /\ _                 = UnknownValidity


-- | How many blocks deep the tx is on the chain
newtype Depth = Depth Int
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (Num, Real, Enum, Integral, Pretty, ToJSON, FromJSON)

instance MeetSemiLattice Depth where
  Depth a /\ Depth b = Depth (max a b)

{- Note [TxStatus state machine]

The status of a transaction is described by the following state machine.

Current state | Next state(s)
-----------------------------------------------------
Unknown       | OnChain
OnChain       | OnChain, Unknown, Committed
Committed     | -

The initial state after submitting the transaction is Unknown.
-}

-- | The status of a Cardano transaction
data TxStatus =
  Unknown -- ^ The transaction is not on the chain. That's all we can say.
  | TentativelyConfirmed Depth TxValidity -- ^ The transaction is on the chain, n blocks deep. It can still be rolled back.
  | Committed TxValidity -- ^ The transaction is on the chain. It cannot be rolled back anymore.
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving Pretty via (PrettyShow TxStatus)

instance MeetSemiLattice TxStatus where
  Unknown /\ a                                             = a
  a /\ Unknown                                             = a
  TentativelyConfirmed d1 v1 /\ TentativelyConfirmed d2 v2 = TentativelyConfirmed (d1 /\ d2) (v1 /\ v2)
  TentativelyConfirmed _ v1 /\ Committed v2                = Committed (v1 /\ v2)
  Committed v1 /\ TentativelyConfirmed _ v2                = Committed (v1 /\ v2)
  Committed v1 /\ Committed v2                             = Committed (v1 /\ v2)

newtype BlockNumber = BlockNumber Word64
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (Num, Real, Enum, Integral, Pretty, ToJSON, FromJSON)

data Diagnostics =
    Diagnostics
        { numTransactions    :: Integer
        , numScripts         :: Integer
        , numAddresses       :: Integer
        , numUnspentOutputs  :: Int
        , numUnmatchedInputs :: Int
        , someTransactions   :: [TxId]
        }
        deriving stock (Eq, Ord, Show, Generic)
        deriving anyclass (ToJSON, FromJSON)

data TxStatusFailure
      -- | We couldn't return the status because the 'TxIdState' was in a ...
      -- state ... that we didn't know how to decode in
      -- 'Plutus.ChainIndex.TxIdState.transactionStatus'.
      = TxIdStateInvalid BlockNumber TxId TxIdState
      | InvalidRollbackAttempt BlockNumber TxId TxIdState
      deriving (Show, Eq)

data TxIdState = TxIdState
  { txnsConfirmed :: Map TxId TxConfirmedState
  -- ^ Number of times this transaction has been added as well as other
  -- necessary metadata.
  , txnsDeleted   :: Map TxId (Sum Int)
  -- ^ Number of times this transaction has been deleted.
  }
  deriving stock (Eq, Generic, Show)

instance Monoid TxIdState where
    mappend = (<>)
    mempty  = TxIdState { txnsConfirmed=mempty, txnsDeleted=mempty }

data TxConfirmedState =
  TxConfirmedState
    { timesConfirmed :: Sum Int
    , blockAdded     :: Last BlockNumber
    , validity       :: Last TxValidity
    }
    deriving stock (Eq, Generic, Show)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid TxConfirmedState)

-- A semigroup instance that merges the two maps, instead of taking the
-- leftmost one.
instance Semigroup TxIdState where
  TxIdState{txnsConfirmed=c, txnsDeleted=d} <> TxIdState{txnsConfirmed=c', txnsDeleted=d'}
    = TxIdState { txnsConfirmed = Map.unionWith (<>) c c'
                , txnsDeleted   = Map.unionWith (<>) d d'
                }

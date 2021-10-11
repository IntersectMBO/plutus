{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-| Misc. types used in this package
-}
module Plutus.ChainIndex.Types(
    BlockId(..)
    , blockId
    , Tip(..)
    , Point(..)
    , pointsToTip
    , tipAsPoint
    , TxValidity(..)
    , TxStatus
    , TxOutStatus
    , RollbackState(..)
    , TxOutState(..)
    , liftTxOutStatus
    , txOutStatusTxOutState
    , BlockNumber(..)
    , Depth(..)
    , Diagnostics(..)
    , TxConfirmedState(..)
    , TxStatusFailure(..)
    , TxIdState(..)
    , TxUtxoBalance(..)
    , tubUnspentOutputs
    , tubUnmatchedSpentInputs
    , TxOutBalance(..)
    , tobUnspentOutputs
    , tobSpentOutputs
    ) where

import           Codec.Serialise                  (Serialise)
import qualified Codec.Serialise                  as CBOR
import           Control.Lens                     (makeLenses)
import           Control.Monad                    (void)
import           Crypto.Hash                      (SHA256, hash)
import           Data.Aeson                       (FromJSON, ToJSON)
import qualified Data.ByteArray                   as BA
import qualified Data.ByteString.Lazy             as BSL
import           Data.Map                         (Map)
import qualified Data.Map                         as Map
import           Data.Monoid                      (Last (..), Sum (..))
import           Data.Semigroup.Generic           (GenericSemigroupMonoid (..))
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Text.Prettyprint.Doc.Extras (PrettyShow (..))
import           Data.Word                        (Word64)
import           GHC.Generics                     (Generic)
import           Ledger                           (TxOutRef (..))
import           Ledger.Blockchain                (Block, BlockId (..))
import           Ledger.Slot                      (Slot)
import           Ledger.TxId                      (TxId)
import           PlutusTx.Lattice                 (MeetSemiLattice (..))
import           Prettyprinter                    (Pretty (..), (<+>))

-- | Compute a hash of the block's contents.
blockId :: Block -> BlockId
blockId = BlockId
        . BA.convert
        . hash @_ @SHA256
        . BSL.toStrict
        . CBOR.serialise

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
newtype Depth = Depth { unDepth :: Int }
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
type TxStatus = RollbackState ()

-- | The rollback state of a Cardano transaction
data RollbackState a =
    Unknown
    -- ^ The transaction is not on the chain. That's all we can say.
  | TentativelyConfirmed Depth TxValidity a
    -- ^ The transaction is on the chain, n blocks deep. It can still be rolled
    -- back.
  | Committed TxValidity a
    -- ^ The transaction is on the chain. It cannot be rolled back anymore.
  deriving stock (Eq, Ord, Show, Generic, Functor)
  deriving anyclass (ToJSON, FromJSON)
  deriving Pretty via (PrettyShow (RollbackState a))

instance MeetSemiLattice a => MeetSemiLattice (RollbackState a) where
  Unknown /\ a = a
  a /\ Unknown = a
  TentativelyConfirmed d1 v1 a1 /\ TentativelyConfirmed d2 v2 a2 =
    TentativelyConfirmed (d1 /\ d2) (v1 /\ v2) (a1 /\ a2)
  TentativelyConfirmed _ v1 a1 /\ Committed v2 a2 = Committed (v1 /\ v2) (a1 /\ a2)
  Committed v1 a1 /\ TentativelyConfirmed _ v2 a2 = Committed (v1 /\ v2) (a1 /\ a2)
  Committed v1 a1 /\ Committed v2 a2 = Committed (v1 /\ v2) (a1 /\ a2)


{- Note [TxOutStatus state machine]

The status of a transaction output is described by the following state machine.

Current state           | Next state(s)
-----------------------------------------------------
TxOutUnknown            | TxOutTentativelyUnspent
TxOutTentativelyUnspent | TxOutUnknown, TxOutTentativelySpent, TxOutConfirmedUnspent
TxOutTentativelySpent   | TxOutUnknown, TxOutConfirmedSpent
TxOutConfirmedUnspent   | TxOutConfirmedSpent
TxOutConfirmedSpent     | -

The initial state after submitting the transaction is 'TxOutUnknown'.
-}

type TxOutStatus = RollbackState TxOutState

data TxOutState = Spent TxId -- Spent by this transaction
                | Unspent
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving Pretty via (PrettyShow TxOutState)

-- | Maybe extract the 'TxOutState' (Spent or Unspent) of a 'TxOutStatus'.
txOutStatusTxOutState :: TxOutStatus -> Maybe TxOutState
txOutStatusTxOutState Unknown                      = Nothing
txOutStatusTxOutState (TentativelyConfirmed _ _ s) = Just s
txOutStatusTxOutState (Committed _ s)              = Just s

-- | Converts a 'TxOutStatus' to a 'TxStatus'. Possible since a transaction
-- output belongs to a transaction.
--
-- Note, however, that we can't convert a 'TxStatus' to a 'TxOutStatus'.
liftTxOutStatus :: TxOutStatus -> TxStatus
liftTxOutStatus = void

newtype BlockNumber = BlockNumber { unBlockNumber :: Word64 }
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

-- | Datatype returned when we couldn't get the state of a tx or a tx output.
data TxStatusFailure
      -- | We couldn't return the status because the 'TxIdState' was in a ...
      -- state ... that we didn't know how to decode in
      -- 'Plutus.ChainIndex.TxIdState.transactionStatus'.
      = TxIdStateInvalid BlockNumber TxId TxIdState
      -- | We couldn't return the status because the 'TxOutBalance' does not
      -- contain the target tx output.
      | TxOutBalanceStateInvalid BlockNumber TxOutRef TxOutBalance
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

-- A semigroup instance that merges the two maps, instead of taking the
-- leftmost one.
instance Semigroup TxIdState where
  TxIdState{txnsConfirmed=c, txnsDeleted=d} <> TxIdState{txnsConfirmed=c', txnsDeleted=d'}
    = TxIdState { txnsConfirmed = Map.unionWith (<>) c c'
                , txnsDeleted   = Map.unionWith (<>) d d'
                }

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

-- | The effect of a transaction (or a number of them) on the tx output set.
data TxOutBalance =
  TxOutBalance
    { _tobUnspentOutputs :: Set TxOutRef
    -- ^ Outputs newly added by the transaction(s)
    , _tobSpentOutputs   :: Map TxOutRef TxId
    -- ^ Outputs spent by the transaction(s) along with the tx id that spent it
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Semigroup TxOutBalance where
    l <> r =
        TxOutBalance
            { _tobUnspentOutputs = _tobUnspentOutputs r
                                <> (_tobUnspentOutputs l `Set.difference` Map.keysSet (_tobSpentOutputs r))
            , _tobSpentOutputs   = _tobSpentOutputs l <> _tobSpentOutputs r
            }

instance Monoid TxOutBalance where
    mappend = (<>)
    mempty = TxOutBalance mempty mempty

makeLenses ''TxOutBalance

-- | The effect of a transaction (or a number of them) on the utxo set.
data TxUtxoBalance =
    TxUtxoBalance
        { _tubUnspentOutputs       :: Set TxOutRef
        -- ^ Outputs newly added by the transaction(s)
        , _tubUnmatchedSpentInputs :: Set TxOutRef
        -- ^ Outputs spent by the transaction(s) that have no matching unspent output
        }
        deriving stock (Eq, Show, Generic)
        deriving anyclass (FromJSON, ToJSON, Serialise)


makeLenses ''TxUtxoBalance

instance Semigroup TxUtxoBalance where
    l <> r =
        TxUtxoBalance
            { _tubUnspentOutputs       = _tubUnspentOutputs r
                                      <> (_tubUnspentOutputs l `Set.difference` _tubUnmatchedSpentInputs r)
            , _tubUnmatchedSpentInputs = (_tubUnmatchedSpentInputs r `Set.difference` _tubUnspentOutputs l)
                                      <> _tubUnmatchedSpentInputs l
            }

instance Monoid TxUtxoBalance where
    mappend = (<>)
    mempty = TxUtxoBalance mempty mempty

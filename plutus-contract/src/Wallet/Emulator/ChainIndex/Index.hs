{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

-- | This module implements an index of transactions
--   by slot and addresses
module Wallet.Emulator.ChainIndex.Index where

import           Data.Aeson        (FromJSON, ToJSON)
import           Data.FingerTree   (FingerTree, Measured (..), (|>))
import qualified Data.FingerTree   as FingerTree
import           Data.Foldable     (foldl', toList)
import           Data.Map.Strict   (Map)
import qualified Data.Map.Strict   as Map
import           Data.Maybe        (fromMaybe)
import           Data.Semigroup    (Max (..))
import           GHC.Generics      (Generic)
import           Ledger.Address    (Address)
import           Ledger.AddressMap (AddressMap)
import qualified Ledger.AddressMap as AM
import           Ledger.Interval   (Extended (..), Interval (..), LowerBound (..), UpperBound (..))
import           Ledger.Slot       (Slot (..), SlotRange)
import           Ledger.Tx         (Tx)
import           Ledger.TxId       (TxId)

-- | The slot in which a transaction was added to the chain.
newtype TxSlot = TxSlot
    {- This is the 'Measure' of 'ChainIndexItem', but the class has a 'Monoid'
       superclass. But 'Max' is only a 'Semigroup' so we add the 'Maybe'.
    -}
    { unTxSlot :: Maybe (Max Slot)
    } deriving stock (Eq, Show, Generic)
      deriving newtype (Semigroup, Monoid)

-- | A transaction with extra information, for the chain index.
data ChainIndexItem = ChainIndexItem
    { ciSlot :: !Slot -- ^ The slot in which the transaction was added to the chain
    , ciTx   :: !Tx -- ^ The transaction
    , ciTxId :: !TxId -- ^ Hash of the transaction
    } deriving stock (Eq, Show, Generic)
      deriving anyclass (ToJSON, FromJSON)

instance Measured TxSlot ChainIndexItem where
    measure ChainIndexItem{ciSlot} =
        TxSlot
            { unTxSlot = Just (Max ciSlot)
            }

-- | A list of transactions that touch an address, sorted by slot number
newtype AddressIndex = AddressIndex{ unAddressIndex :: FingerTree TxSlot ChainIndexItem }
    deriving (Eq, Show)

instance Semigroup AddressIndex where
    -- Warning: @l <> r@ keeps the order of slots, but inside each slot
    -- all transactions of @l@ will appear before all transactions of @r@.
    -- TODO: We should probably keep track of block numbers as well as slot numbers!
    l <> (AddressIndex r) = foldl' (flip insertAI) l (toList r)

instance Monoid AddressIndex where
    mappend = (<>)
    mempty  = AddressIndex mempty

-- | Insert a new item into the chain index.
insertAI :: ChainIndexItem -> AddressIndex -> AddressIndex
insertAI itm ix =
    let (AddressIndex before, AddressIndex after) = split (ciSlot itm) ix
    in AddressIndex $ (before |> itm) <> after

-- | Split the address index into two. The first of the results
--   has all entries up to and including the slot. The second result has all
--   entries after the given slot.
split :: Slot -> AddressIndex -> (AddressIndex, AddressIndex)
split sl (AddressIndex ix) =
    let
        gt TxSlot{unTxSlot} = maybe False (\(Max sl') -> sl' > sl) unTxSlot
        (before, after) = FingerTree.split gt ix
    in (AddressIndex before, AddressIndex after)

newtype ChainIndex = ChainIndex { unChainIndex :: Map Address AddressIndex }
    deriving (Eq,Show, Generic)

-- | An empty chain index.
emptyCI :: ChainIndex
emptyCI = ChainIndex mempty

instance Semigroup ChainIndex where
    ChainIndex l <> ChainIndex r =
        ChainIndex $ Map.unionWith (<>) l r

instance Monoid ChainIndex where
    mappend = (<>)
    mempty = ChainIndex mempty

-- | Insert a transaction into the 'ChainIndex'
insert :: AddressMap -> ChainIndexItem -> ChainIndex -> ChainIndex
insert am item (ChainIndex ci) =
    let keys = toList (AM.addressesTouched am (ciTx item))
        alt = Just . insertAI item . fromMaybe mempty
    in ChainIndex (foldl' (\ci' addr -> Map.alter alt addr ci') ci keys)

-- | All transactions that modify the address, from a given slot onwards
transactionsAt :: ChainIndex -> SlotRange -> Address -> [ChainIndexItem]
transactionsAt (ChainIndex mp) sl addr = let
    allItems = Map.findWithDefault mempty addr mp
    result = case sl of
        Interval (LowerBound (Finite s1) in1) (UpperBound (Finite s2) in2) ->
            let low = if in1 then s1 else pred s1
                high = if in2 then pred s2 else s2
            in fst $ split low $ snd $ split high allItems
        Interval (LowerBound NegInf _) (UpperBound (Finite s2) in2) ->
            let high = if in2 then s2 else pred s2
            in  fst $ split high allItems
        Interval (LowerBound (Finite s1) in1) (UpperBound PosInf _) ->
            let low = if in1 then pred s1 else s1
            in  snd $ split low allItems
        Interval (LowerBound NegInf _) (UpperBound PosInf _) -> allItems
        Interval _ _ -> allItems

    in toList $ unAddressIndex result

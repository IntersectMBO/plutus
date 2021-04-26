{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

-- | Support for visualisation of a blockchain as a graph.
module Wallet.Graph
  ( txnFlows
  , graph
  , FlowGraph
  , FlowLink
  , TxRef
  , UtxOwner
  , UtxoLocation
  ) where

import           Data.Aeson.Types  (ToJSON, toJSON)
import           Data.List         (nub)
import qualified Data.Map          as Map
import           Data.Maybe        (catMaybes)
import qualified Data.Set          as Set
import qualified Data.Text         as Text
import           GHC.Generics      (Generic)

import qualified Ledger.Ada        as Ada
import           Ledger.Address
import           Ledger.Blockchain
import           Ledger.Credential (Credential (..))
import           Ledger.Crypto
import           Ledger.Tx
import           Ledger.TxId

-- | The owner of an unspent transaction output.
data UtxOwner
  = PubKeyOwner PubKey
    -- ^ Funds owned by a known public key.
  | ScriptOwner
    -- ^ Funds locked by script.
  | OtherOwner
    -- ^ All other funds (that is, funds owned by a public key we are not interested in).
  deriving (Eq, Ord, Show, Generic, ToJSON)

-- | Given a set of known public keys, compute the owner of a given transaction output.
owner :: Set.Set PubKey -> TxOut -> UtxOwner
owner keys TxOut {txOutAddress=Address{addressCredential}} =
  let hashMap = foldMap (\pk -> Map.singleton (pubKeyHash pk) pk) keys
  in case addressCredential of
    ScriptCredential{}                                       -> ScriptOwner
    PubKeyCredential pkh | Just pk <- Map.lookup pkh hashMap -> PubKeyOwner pk
    _                                                        -> OtherOwner

-- | A wrapper around the first 8 digits of a 'TxId'.
newtype TxRef =
  TxRef Text.Text
  deriving (Eq, Ord, Show, Generic)

instance ToJSON TxRef where
  toJSON (TxRef t) = toJSON t

mkRef :: TxId -> TxRef
mkRef = TxRef . Text.pack . take 8 . show . getTxId

-- | The location of a transaction in a blockchain specified by two indices: the index of the containing
-- block in the chain, and the index of the transaction within the block.
data UtxoLocation = UtxoLocation
  { utxoLocBlock    :: Integer
  , utxoLocBlockIdx :: Integer
  } deriving (Eq, Ord, Show, Generic, ToJSON)

-- | A link in the flow graph.
data FlowLink = FlowLink
  { flowLinkSource    :: TxRef -- ^ The source transaction.
  , flowLinkTarget    :: TxRef -- ^ The target transaction.
  , flowLinkValue     :: Integer -- ^ The value of Ada along this edge.
  , flowLinkOwner     :: UtxOwner -- ^ The owner of this edge.
  , flowLinkSourceLoc :: UtxoLocation -- ^ The location of the source transaction.
  , flowLinkTargetLoc :: Maybe UtxoLocation -- ^ The location of the target transaction, if 'Nothing' then it is unspent.
  } deriving (Show, Generic, ToJSON)

-- | The flow graph, consisting of a set of nodes ('TxRef's) and edges ('FlowLink's).
data FlowGraph = FlowGraph
  { flowGraphLinks :: [FlowLink]
  , flowGraphNodes :: [TxRef]
  } deriving (Show, Generic, ToJSON)

-- | Construct a graph from a list of 'FlowLink's.
graph :: [FlowLink] -> FlowGraph
graph lnks = FlowGraph {..}
  where
    flowGraphLinks = lnks
    flowGraphNodes = nub $ fmap flowLinkSource lnks ++ fmap flowLinkTarget lnks

-- | Compute the 'FlowLink's for a 'Blockchain' given a set of known 'PubKey's.
txnFlows :: [PubKey] -> Blockchain -> [FlowLink]
txnFlows keys bc = catMaybes (utxoLinks ++ foldMap extract bc')
  where
    bc' = foldMap (\(blockNum, txns) -> fmap (\(blockIdx, txn) -> (UtxoLocation blockNum blockIdx, txn)) txns) $ zipWithIndex $ zipWithIndex <$> reverse bc

    sourceLocations :: Map.Map TxOutRef UtxoLocation
    sourceLocations = Map.fromList $ foldMap (uncurry outRefsWithLoc) bc'

    knownKeys :: Set.Set PubKey
    knownKeys = Set.fromList keys

    utxos = fmap fst $ Map.toList $ unspentOutputs bc
    utxoLinks = uncurry (flow Nothing) <$> zip (utxoTargets <$> utxos) utxos

    extract :: (UtxoLocation, OnChainTx) -> [Maybe FlowLink]
    extract (loc, tx) =
      let targetRef = mkRef $ eitherTx txId txId tx in
      fmap (flow (Just loc) targetRef . txInRef) (Set.toList $ consumableInputs tx)
    -- make a flow for a TxOutRef

    flow :: Maybe UtxoLocation -> TxRef -> TxOutRef -> Maybe FlowLink
    flow tgtLoc tgtRef rf = do
      src <- out bc rf
      sourceLoc <- Map.lookup rf sourceLocations
      let sourceRef = mkRef $ txOutRefId rf
      pure FlowLink
            { flowLinkSource = sourceRef
            , flowLinkTarget = tgtRef
            , flowLinkValue = fromIntegral $ Ada.fromValue $ txOutValue src
            , flowLinkOwner = owner knownKeys src
            , flowLinkSourceLoc = sourceLoc
            , flowLinkTargetLoc = tgtLoc
            }

    zipWithIndex = zip [1..]

-- | Annotate the 'TxOutRef's produced by a transaction with the location of the transaction.
outRefsWithLoc :: UtxoLocation -> OnChainTx -> [(TxOutRef, UtxoLocation)]
outRefsWithLoc loc (Valid tx) = (\txo -> (snd txo, loc)) <$> txOutRefs tx
outRefsWithLoc _ (Invalid _)  = []

-- | Create a 'TxRef' from a 'TxOutRef'.
utxoTargets :: TxOutRef -> TxRef
utxoTargets (TxOutRef rf idx) = TxRef $ Text.unwords ["utxo", Text.pack $ take 8 $ show $ getTxId rf, Text.pack $ show idx]

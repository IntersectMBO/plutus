{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

-- | Support for visualisation of a mockchain as a graph.
module Wallet.Graph
  ( txnFlows
  , graph
  , FlowGraph
  , FlowLink
  , TxRef
  , UtxOwner
  , UtxoLocation
  ) where

import           Data.Aeson.Types (ToJSON, toJSON)
import           Data.List        (nub)
import qualified Data.Map         as Map
import           Data.Maybe       (catMaybes)
import qualified Data.Set         as Set
import qualified Data.Text        as Text
import           GHC.Generics     (Generic)
import           Ledger.Types     (Blockchain, PubKey, Tx, TxId, TxOutOf (TxOutOf), TxOutRef, TxOutRefOf (TxOutRefOf),
                                   TxOutType (PayToPubKey, PayToScript), getTxId, hashTx, out, txInRef, txInputs,
                                   txOutRefId, txOutRefs, txOutType, txOutValue, unspentOutputs)

-- | Owner of unspent funds
data UtxOwner
  = PubKeyOwner PubKey
    -- ^ Funds owned by a known public key
  | ScriptOwner
    -- ^ Funds locked by script
  | OtherOwner
    -- ^ All other funds (that is, funds owned by a public key we are not interested in )
  deriving (Eq, Ord, Show, Generic, ToJSON)

owner :: Set.Set PubKey -> TxOutOf h -> UtxOwner
owner keys TxOutOf {..} =
  case txOutType of
    PayToScript _ -> ScriptOwner
    PayToPubKey pk
      | pk `Set.member` keys -> PubKeyOwner pk
    _ -> OtherOwner

-- | Wrapper around the first 8 digits of a `TxId`
newtype TxRef =
  TxRef Text.Text
  deriving (Eq, Ord, Show, Generic)

instance ToJSON TxRef where
  toJSON (TxRef t) = toJSON t

mkRef :: TxId -> TxRef
mkRef = TxRef . Text.pack . take 8 . show . getTxId

data UtxoLocation = UtxoLocation
  { utxoLocBlock    :: Integer
  , utxoLocBlockIdx :: Integer
  } deriving (Eq, Ord, Show, Generic, ToJSON)

data FlowLink = FlowLink
  { flowLinkSource    :: TxRef
  , flowLinkTarget    :: TxRef
  , flowLinkValue     :: Integer
  , flowLinkOwner     :: UtxOwner
  , flowLinkSourceLoc :: UtxoLocation
  , flowLinkTargetLoc :: Maybe UtxoLocation
    -- ^ If this is `Nothing` then the output is unspent (UTXO)
  } deriving (Show, Generic, ToJSON)

data FlowGraph = FlowGraph
  { flowGraphLinks :: [FlowLink]
  , flowGraphNodes :: [TxRef]
  } deriving (Generic, ToJSON)

graph :: [FlowLink] -> FlowGraph
graph lnks = FlowGraph {..}
  where
    flowGraphLinks = lnks
    flowGraphNodes = nub $ fmap flowLinkSource lnks ++ fmap flowLinkTarget lnks

-- | The flows of value from t
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

    extract :: (UtxoLocation, Tx) -> [Maybe FlowLink]
    extract (loc, tx) =
      let targetRef = mkRef $ hashTx tx in
      fmap (flow (Just loc) targetRef . txInRef) (Set.toList $ txInputs tx)
    -- make a flow for a TxOutRef

    flow :: Maybe UtxoLocation -> TxRef -> TxOutRef -> Maybe FlowLink
    flow tgtLoc tgtRef rf = do
      src <- out bc rf
      sourceLoc <- Map.lookup rf sourceLocations
      let sourceRef = mkRef $ txOutRefId rf
      pure FlowLink
            { flowLinkSource = sourceRef
            , flowLinkTarget = tgtRef
            , flowLinkValue = fromIntegral $ txOutValue src
            , flowLinkOwner = owner knownKeys src
            , flowLinkSourceLoc = sourceLoc
            , flowLinkTargetLoc = tgtLoc
            }

    zipWithIndex = zip [1..]

-- | Annotate the [[TxOutRef]]s produced by a transaction with their location
outRefsWithLoc :: UtxoLocation -> Tx -> [(TxOutRef, UtxoLocation)]
outRefsWithLoc loc tx = (\txo -> (snd txo, loc)) <$> txOutRefs tx

utxoTargets :: Show a => TxOutRefOf a -> TxRef
utxoTargets (TxOutRefOf rf idx) = TxRef $ Text.unwords ["utxo", Text.pack $ take 8 $ show $ getTxId rf, Text.pack $ show idx]

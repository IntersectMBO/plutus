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
  ) where

import           Data.Aeson.Types (ToJSON, toJSON)
import           Data.Foldable    (fold)
import           Data.List        (nub)
import qualified Data.Map         as Map
import qualified Data.Set         as Set
import qualified Data.Text        as Text
import           GHC.Generics     (Generic)
import           Ledger.Types     (Blockchain, PubKey, TxId', TxOut (TxOut), TxOutRef (TxOutRef),
                                   TxOutType (PayToPubKey, PayToScript), getTxId, hashTx, out, txInRef, txInputs,
                                   txOutRefId, txOutType, txOutValue, unspentOutputs)

-- | Owner of unspent funds
data UtxOwner
  = PubKeyOwner PubKey
    -- ^ Funds owned by a known public key
  | ScriptOwner
    -- ^ Funds locked by script
  | OtherOwner
    -- ^ All other funds (that is, funds owned by a public key we are not interested in )
  deriving (Eq, Ord, Show, Generic, ToJSON)

owner :: Set.Set PubKey -> TxOut h -> UtxOwner
owner keys TxOut {..} =
  case txOutType of
    PayToScript _ -> ScriptOwner
    PayToPubKey pk
      | pk `Set.member` keys -> PubKeyOwner pk
    _ -> OtherOwner

-- | Wrapper around the first 8 digits of a `TxId'`
newtype TxRef =
  TxRef Text.Text
  deriving (Eq, Ord, Show, Generic)

instance ToJSON TxRef where
  toJSON (TxRef t) = toJSON t

mkRef :: TxId' -> TxRef
mkRef = TxRef . Text.pack . take 8 . show . getTxId

data FlowLink = FlowLink
  { flowLinkSource :: TxRef
  , flowLinkTarget :: TxRef
  , flowLinkValue  :: Integer
  , flowLinkOwner  :: UtxOwner
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
txnFlows keys bc = utxoLinks ++ foldMap extract (fold bc)
  where
    knownKeys = Set.fromList keys
    getOut rf =
      let Just o = out bc rf
       in o
    utxos = fmap fst $ Map.toList $ unspentOutputs bc
    utxoLinks = uncurry flow <$> zip (utxoTargets <$> utxos) utxos
    utxoTargets (TxOutRef rf idx) =
      TxRef $
      Text.unwords
        ["utxo", Text.pack $ take 8 $ show $getTxId rf, Text.pack $ show idx]
    extract tx =
      fmap (flow (mkRef $ hashTx tx) . txInRef) (Set.toList $ txInputs tx)
    -- make a flow for a TxOutRef
    flow tgt rf =
      let src = getOut rf
       in FlowLink
            { flowLinkSource = mkRef $ txOutRefId rf -- source :: TxRe
            , flowLinkTarget = tgt -- target :: TxRef
            , flowLinkValue = fromIntegral $ txOutValue src
            , flowLinkOwner = owner knownKeys src
            }

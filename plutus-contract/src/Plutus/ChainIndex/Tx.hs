{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-| The chain index' version of a transaction
-}
module Plutus.ChainIndex.Tx(
    ChainIndexTx(..)
    , fromOnChainTx
    , txOutRefs
    -- ** Lenses
    , citxInputs
    , citxOutputs
    , citxValidRange
    , citxData
    , citxRedeemers
    , citxMintingPolicies
    , citxValidators
    , citxTxId
    ) where

import           Control.Lens (makeLenses)
import           Data.Map     (Map)
import qualified Data.Map     as Map
import           Data.Set     (Set)
import qualified Data.Set     as Set
import           GHC.Generics (Generic)
import           Ledger       (Datum, DatumHash, MintingPolicy, MintingPolicyHash, OnChainTx (..), Redeemer (..),
                               RedeemerHash, SlotRange, Tx (..), TxId, TxIn (txInType), TxInType (..), TxOut,
                               TxOutRef (..), Validator, ValidatorHash, datumHash, mintingPolicyHash, redeemerHash,
                               txId, validatorHash)

data ChainIndexTx = ChainIndexTx {
    _citxTxId            :: TxId,
    _citxInputs          :: Set TxIn,
    _citxOutputs         :: [TxOut],
    _citxValidRange      :: !SlotRange,
    _citxData            :: Map DatumHash Datum,
    _citxRedeemers       :: Map RedeemerHash Redeemer,
    _citxMintingPolicies :: Map MintingPolicyHash MintingPolicy,
    _citxValidators      :: Map ValidatorHash Validator
    } deriving (Show, Eq, Generic)

makeLenses ''ChainIndexTx

txOutRefs :: ChainIndexTx -> [(TxOut, TxOutRef)]
txOutRefs ChainIndexTx{_citxTxId, _citxOutputs} =
    map (\(output, idx) -> (output, TxOutRef _citxTxId idx)) $ zip _citxOutputs [0..]

fromOnChainTx :: OnChainTx -> ChainIndexTx
fromOnChainTx = \case
    Valid tx@Tx{txInputs, txOutputs, txValidRange, txData, txMintScripts} ->
        let (validatorHashes, otherDataHashes, redeemers) = validators txInputs in
        ChainIndexTx
            { _citxTxId = txId tx
            , _citxInputs = txInputs
            , _citxOutputs = txOutputs
            , _citxValidRange = txValidRange
            , _citxData = txData <> otherDataHashes
            , _citxRedeemers = redeemers
            , _citxMintingPolicies = mintingPolicies txMintScripts
            , _citxValidators = validatorHashes
            }
    Invalid tx@Tx{txCollateral, txValidRange, txData, txInputs, txMintScripts} ->
        let (validatorHashes, otherDataHashes, redeemers) = validators txInputs in
        ChainIndexTx
            { _citxTxId = txId tx
            , _citxInputs = txCollateral
            , _citxOutputs = mempty
            , _citxValidRange = txValidRange
            , _citxData = txData <> otherDataHashes
            , _citxRedeemers = redeemers
            , _citxMintingPolicies = mintingPolicies txMintScripts
            , _citxValidators = validatorHashes
            }

mintingPolicies :: Set MintingPolicy -> Map MintingPolicyHash MintingPolicy
mintingPolicies =
    let withHash mps = (mintingPolicyHash mps, mps) in
    Map.fromList . fmap withHash . Set.toList

validators :: Set TxIn -> (Map ValidatorHash Validator, Map DatumHash Datum, Map RedeemerHash Redeemer)
validators =
    let withHash (ConsumeScriptAddress val red dat) =
            ( Map.singleton (validatorHash val) val
            , Map.singleton (datumHash dat) dat
            , Map.singleton (redeemerHash red) red
            )
        withHash ConsumePublicKeyAddress    = mempty
    in foldMap (maybe mempty withHash . txInType) . Set.toList

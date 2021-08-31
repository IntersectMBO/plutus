{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-| The chain index' version of a transaction
-}
module Plutus.ChainIndex.Tx(
    ChainIndexTx(..)
    , ChainIndexTxOutputs(..)
    , fromOnChainTx
    , txOutRefs
    , txOutsWithRef
    , txOutRefMap
    , txOutRefMapForAddr
    -- ** Lenses
    , citxTxId
    , citxInputs
    , citxOutputs
    , citxValidRange
    , citxData
    , citxRedeemers
    , citxMintingPolicies
    , citxStakeValidators
    , citxValidators
    , _InvalidTx
    , _ValidTx
    ) where

import           Control.Lens              (makeLenses, makePrisms)
import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Map                  (Map)
import qualified Data.Map                  as Map
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Data.Text.Prettyprint.Doc
import           Data.Tuple                (swap)
import           GHC.Generics              (Generic)
import           Ledger                    (Address, Datum, DatumHash, MintingPolicy, MintingPolicyHash, OnChainTx (..),
                                            Redeemer (..), RedeemerHash, SlotRange, StakeValidator, StakeValidatorHash,
                                            Tx (..), TxId, TxIn (txInType), TxInType (..), TxOut (txOutAddress),
                                            TxOutRef (..), Validator, ValidatorHash, datumHash, mintingPolicyHash,
                                            redeemerHash, txId, validatorHash)

-- | List of outputs of a transaction. There are no outputs if the transaction
-- is invalid.
data ChainIndexTxOutputs =
    InvalidTx -- ^ The transaction is invalid so there is no outputs
  | ValidTx [TxOut]
  deriving (Show, Eq, Generic, ToJSON, FromJSON)

makePrisms ''ChainIndexTxOutputs

data ChainIndexTx = ChainIndexTx {
    _citxTxId            :: TxId,
    -- ^ The id of this transaction.
    _citxInputs          :: Set TxIn,
    -- ^ The inputs to this transaction.
    _citxOutputs         :: ChainIndexTxOutputs,
    -- ^ The outputs of this transaction, ordered so they can be referenced by index.
    _citxValidRange      :: !SlotRange,
    -- ^ The 'SlotRange' during which this transaction may be validated.
    _citxData            :: Map DatumHash Datum,
    -- ^ Datum objects recorded on this transaction.
    _citxRedeemers       :: Map RedeemerHash Redeemer,
    -- ^ Redeemers of the minting scripts.
    _citxMintingPolicies :: Map MintingPolicyHash MintingPolicy,
    -- ^ The scripts used to check minting conditions.
    _citxStakeValidators :: Map StakeValidatorHash StakeValidator,
    _citxValidators      :: Map ValidatorHash Validator
    } deriving (Show, Eq, Generic, ToJSON, FromJSON)

makeLenses ''ChainIndexTx

instance Pretty ChainIndexTx where
    pretty ChainIndexTx{_citxTxId, _citxInputs, _citxOutputs = ValidTx outputs, _citxValidRange, _citxMintingPolicies, _citxData, _citxRedeemers} =
        let lines' =
                [ hang 2 (vsep ("inputs:" : fmap pretty (Set.toList _citxInputs)))
                , hang 2 (vsep ("outputs:" : fmap pretty outputs))
                , hang 2 (vsep ("minting policies:": fmap (pretty . fst) (Map.toList _citxMintingPolicies)))
                , "validity range:" <+> viaShow _citxValidRange
                , hang 2 (vsep ("data:": fmap (pretty . snd) (Map.toList _citxData) ))
                , hang 2 (vsep ("redeemers:": fmap (pretty . snd) (Map.toList _citxRedeemers) ))
                ]
        in nest 2 $ vsep ["Valid tx" <+> pretty _citxTxId <> colon, braces (vsep lines')]
    pretty ChainIndexTx{_citxTxId, _citxInputs, _citxOutputs = InvalidTx, _citxValidRange, _citxMintingPolicies, _citxData, _citxRedeemers} =
        let lines' =
                [ hang 2 (vsep ("inputs:" : fmap pretty (Set.toList _citxInputs)))
                , hang 2 (vsep ["no outputs:"])
                , hang 2 (vsep ("minting policies:": fmap (pretty . fst) (Map.toList _citxMintingPolicies)))
                , "validity range:" <+> viaShow _citxValidRange
                , hang 2 (vsep ("data:": fmap (pretty . snd) (Map.toList _citxData) ))
                , hang 2 (vsep ("redeemers:": fmap (pretty . snd) (Map.toList _citxRedeemers) ))
                ]
        in nest 2 $ vsep ["Invalid tx" <+> pretty _citxTxId <> colon, braces (vsep lines')]

-- | Get tx output references from tx.
txOutRefs :: ChainIndexTx -> [TxOutRef]
txOutRefs ChainIndexTx { _citxTxId, _citxOutputs = ValidTx outputs } =
    map (\idx -> TxOutRef _citxTxId idx) [0 .. fromIntegral $ length outputs - 1]
txOutRefs ChainIndexTx{_citxOutputs = InvalidTx} = []

-- | Get tx output references and tx outputs from tx.
txOutsWithRef :: ChainIndexTx -> [(TxOut, TxOutRef)]
txOutsWithRef tx@ChainIndexTx { _citxOutputs = ValidTx outputs } = zip outputs $ txOutRefs tx
txOutsWithRef ChainIndexTx { _citxOutputs = InvalidTx }          = []

-- | Get 'Map' of tx outputs references to tx.
txOutRefMap :: ChainIndexTx -> Map TxOutRef (TxOut, ChainIndexTx)
txOutRefMap tx =
    fmap (, tx) $ Map.fromList $ fmap swap $ txOutsWithRef tx

-- | Get 'Map' of tx outputs from tx for a specific address.
txOutRefMapForAddr :: Address -> ChainIndexTx -> Map TxOutRef (TxOut, ChainIndexTx)
txOutRefMapForAddr addr tx =
    Map.filter ((==) addr . txOutAddress . fst) $ txOutRefMap tx

-- | Convert a 'OnChainTx' to a 'ChainIndexTx'. An invalid 'OnChainTx' will not
-- produce any 'ChainIndexTx' outputs and the collateral inputs of the
-- 'OnChainTx' will be the inputs of the 'ChainIndexTx'.
fromOnChainTx :: OnChainTx -> ChainIndexTx
fromOnChainTx = \case
    Valid tx@Tx{txInputs, txOutputs, txValidRange, txData, txMintScripts} ->
        let (validatorHashes, otherDataHashes, redeemers) = validators txInputs in
        ChainIndexTx
            { _citxTxId = txId tx
            , _citxInputs = txInputs
            , _citxOutputs = ValidTx txOutputs
            , _citxValidRange = txValidRange
            , _citxData = txData <> otherDataHashes
            , _citxRedeemers = redeemers
            , _citxMintingPolicies = mintingPolicies txMintScripts
            , _citxStakeValidators = mempty
            , _citxValidators = validatorHashes
            }
    Invalid tx@Tx{txCollateral, txValidRange, txData, txInputs, txMintScripts} ->
        let (validatorHashes, otherDataHashes, redeemers) = validators txInputs in
        ChainIndexTx
            { _citxTxId = txId tx
            , _citxInputs = txCollateral
            , _citxOutputs = InvalidTx
            , _citxValidRange = txValidRange
            , _citxData = txData <> otherDataHashes
            , _citxRedeemers = redeemers
            , _citxMintingPolicies = mintingPolicies txMintScripts
            , _citxStakeValidators = mempty
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

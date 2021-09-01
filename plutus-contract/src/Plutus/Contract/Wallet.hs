{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
-- | Turn 'UnbalancedTx' values into transactions using the
--   wallet API.
module Plutus.Contract.Wallet(
      balanceTx
    , handleTx
    , getUnspentOutput
    , WAPI.signTxAndSubmit
    -- * Exporting transactions
    , ExportTx(..)
    , ExportTxInput(..)
    , export
    ) where

import qualified Cardano.Api                 as C
import qualified Cardano.Api.Shelley         as C
import           Control.Monad               ((>=>))
import           Control.Monad.Error.Lens    (throwing)
import           Control.Monad.Freer         (Eff, Member)
import           Control.Monad.Freer.Error   (Error, throwError)
import           Data.Aeson                  (FromJSON (..), ToJSON (..), Value (Object), object, (.:), (.=))
import           Data.Bitraversable          (bitraverse)
import           Data.ByteArray.Encoding     (Base (Base16), convertToBase)
import           Data.Map                    (Map)
import qualified Data.Map                    as Map
import           Data.Maybe                  (mapMaybe)
import           Data.Proxy                  (Proxy (..))
import qualified Data.Set                    as Set
import           Data.Text                   (Text)
import qualified Data.Text.Encoding          as Text
import           Data.Typeable               (Typeable)
import           Data.Void                   (Void)
import           GHC.Generics                (Generic)
import qualified Ledger                      as Plutus
import qualified Ledger.Ada                  as Ada
import           Ledger.Bytes                (LedgerBytes (..))
import           Ledger.Constraints          (mustPayToPubKey)
import           Ledger.Constraints.OffChain (UnbalancedTx (..), mkTx)
import           Ledger.Crypto               (PubKey (..), pubKeyHash)
import           Ledger.Tx                   (Tx (..), TxOutRef, txInRef)
import qualified Plutus.Contract.CardanoAPI  as CardanoAPI
import qualified Plutus.Contract.Request     as Contract
import           Plutus.Contract.Types       (Contract (..))
import qualified Wallet.API                  as WAPI
import           Wallet.Effects              (WalletEffect, balanceTx)
import           Wallet.Emulator.Error       (WalletAPIError)
import           Wallet.Types                (AsContractError (_ConstraintResolutionError, _OtherError))

{- Note [Submitting transactions from Plutus contracts]

'UnbalancedTx' is the type of transactions that meet some set of constraints
(produced by 'Ledger.Constraints.OffChain.mkTx'), but can't be submitted to
the ledger yet because they may not be balanced and they lack signatures and
fee payments. To turn an 'UnbalancedTx' value into a valid transaction that can
be submitted to the network, the contract backend needs to

* Balance it.
  If the total value of 'txInputs' + the 'txMint' field is
  greater than the total value of 'txOutputs', then one or more public key
  outputs need to be added. How many and what addresses they are is up
  to the wallet (probably configurable).
  If the total balance 'txInputs' + the 'txMint' field is less than
  the total value of 'txOutputs', then one or more public key inputs need
  to be added (and potentially some outputs for the change).

* Compute fees.
  Once the final size of the transaction is known, the fees for the transaction
  can be computed. The transaction fee needs to be paid for with additional
  inputs so I assume that this step and the previous step will be combined.

  Also note that even if the 'UnbalancedTx' that we get from the contract
  endpoint happens to be balanced already, we still need to add fees to it. So
  we can't skip the balancing & fee computation step.

  Balancing and coin selection will eventually be performed by the wallet
  backend.

* Sign it.
  The signing process needs to provide signatures for all public key
  inputs in the balanced transaction, and for all public keys in the
  'unBalancedTxRequiredSignatories' field.

-}

-- | Balance an unabalanced transaction, sign it, and submit
--   it to the chain in the context of a wallet.
handleTx ::
    ( Member WalletEffect effs
    , Member (Error WalletAPIError) effs
    )
    => UnbalancedTx -> Eff effs Tx
handleTx = balanceTx >=> either throwError WAPI.signTxAndSubmit

-- | Get an unspent output belonging to the wallet.
getUnspentOutput :: AsContractError e => Contract w s e TxOutRef
getUnspentOutput = do
    ownPK <- Contract.ownPubKey
    let constraints = mustPayToPubKey (pubKeyHash ownPK) (Ada.lovelaceValueOf 1)
    utx <- either (throwing _ConstraintResolutionError) pure (mkTx @Void mempty constraints)
    tx <- Contract.balanceTx utx
    case Set.lookupMin (txInputs tx) of
        Just inp -> pure $ txInRef inp
        Nothing  -> throwing _OtherError "Balanced transaction has no inputs"

-- | Partial transaction that can be balanced by the wallet backend.
data ExportTx =
        ExportTx
            { partialTx   :: C.Tx C.AlonzoEra -- ^ The transaction itself
            , lookups     :: [ExportTxInput] -- ^ The tx outputs for all inputs spent by the partial tx
            , signatories :: [Text] -- ^ Key(s) that we expect to be used for balancing & signing. (Advisory) See note [Keys in ExportT]
            }
    deriving stock (Generic, Typeable)

data ExportTxInput = ExportTxInput{txIn :: C.TxIn, txOut :: C.TxOut C.AlonzoEra}
    deriving stock (Generic, Typeable)
    deriving anyclass (ToJSON)

instance ToJSON ExportTx where
    toJSON ExportTx{partialTx, lookups, signatories} =
        object
            [ "transaction" .= toJSON (C.serialiseToTextEnvelope Nothing partialTx)
            , "inputs"      .= toJSON lookups
            , "signatories" .= toJSON signatories
            ]

instance FromJSON ExportTx where
    parseJSON (Object v) =
        ExportTx
            <$> ((v .: "transaction") >>= either (fail . show) pure . C.deserialiseFromTextEnvelope (C.proxyToAsType Proxy))
            <*> pure mempty -- FIXME: How to deserialise Utxo / [(TxIn, TxOut)] ) see https://github.com/input-output-hk/cardano-node/issues/3051
            <*> v .: "signatories"
    parseJSON _ = fail "Expexted Object"

export :: C.ProtocolParameters -> C.NetworkId -> UnbalancedTx -> Either CardanoAPI.ToCardanoError ExportTx
export params networkId UnbalancedTx{unBalancedTxTx, unBalancedTxUtxoIndex, unBalancedTxRequiredSignatories} =
    ExportTx
        <$> mkPartialTx params networkId unBalancedTxTx
        <*> mkLookups networkId unBalancedTxUtxoIndex
        <*> mkSignatories unBalancedTxRequiredSignatories

mkPartialTx :: C.ProtocolParameters -> C.NetworkId -> Plutus.Tx -> Either CardanoAPI.ToCardanoError (C.Tx C.AlonzoEra)
mkPartialTx params networkId = fmap (C.makeSignedTransaction []) . CardanoAPI.toCardanoTxBody (Just params) networkId

mkLookups :: C.NetworkId -> Map Plutus.TxOutRef Plutus.TxOut -> Either CardanoAPI.ToCardanoError [ExportTxInput]
mkLookups networkId = fmap (fmap $ uncurry ExportTxInput) . traverse (bitraverse CardanoAPI.toCardanoTxIn (CardanoAPI.toCardanoTxOut networkId)) . Map.toList

mkSignatories :: Map Plutus.PubKeyHash (Maybe Plutus.PubKey) -> Either CardanoAPI.ToCardanoError [Text]
mkSignatories =
    -- see note [Keys in ExportTx]
    Right . fmap (\(PubKey (LedgerBytes k)) -> Text.decodeUtf8 $ convertToBase Base16 (k <> k)) . mapMaybe snd . Map.toList

{- Note [Keys in ExportTx]

The wallet backend (receiver of 'ExportTx' values) expectes the public keys in the
'signatories' field to be 'Cardano.Crypto.Wallet.XPub' keys - extended public keys
of 64 bytes. In the emulator we only deal with ED25519 keys of 32 bytes. Until that
is changed (https://jira.iohk.io/browse/SCP-2644) we simply append each of our keys
to itself in order to get a key of the correct length.

-}

module Chain.Types where

import Prelude
import Clipboard (Action) as Clipboard
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Fold', Iso', Lens', Prism', Traversal', filtered, preview, prism', traversed)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Plutus.V1.Ledger.Address (Address(..))
import Plutus.V1.Ledger.Crypto (PubKey, Signature)
import Plutus.V1.Ledger.Interval (Interval)
import Plutus.V1.Ledger.Slot (Slot)
import Plutus.V1.Ledger.Tx (Tx, TxIn, TxOut(..), TxOutRef(..))
import Plutus.V1.Ledger.TxId (TxId)
import Plutus.V1.Ledger.Value (Value)
import Wallet.Rollup.Types (AnnotatedTx(..), BeneficialOwner(..), DereferencedInput, SequenceId, TxKey, _TxKey)

data Action
  = FocusTx (Maybe TxId)
  | ClipboardAction Clipboard.Action

derive instance genericChainFocus :: Generic Action _

instance showChainFocus :: Show Action where
  show = genericShow

_FocusTx :: Prism' Action TxId
_FocusTx = prism' set get
  where
  get (FocusTx txId) = txId

  get _ = Nothing

  set = FocusTx <<< Just

newtype AnnotatedBlockchain
  = AnnotatedBlockchain (Array (Array AnnotatedTx))

derive instance newtypeAnnotatedBlockchain :: Newtype AnnotatedBlockchain _

_AnnotatedBlockchain :: Iso' AnnotatedBlockchain (Array (Array AnnotatedTx))
_AnnotatedBlockchain = _Newtype

_AnnotatedBlocks :: Traversal' AnnotatedBlockchain AnnotatedTx
_AnnotatedBlocks = _AnnotatedBlockchain <<< traversed <<< traversed

type State
  = { chainFocus :: Maybe TxId
    , chainFocusAppearing :: Boolean
    , chainFocusAge :: Ordering
    }

initialState :: State
initialState =
  { chainFocus: Nothing
  , chainFocusAppearing: false
  , chainFocusAge: EQ
  }

_chainFocus :: forall r a. Lens' { chainFocus :: a | r } a
_chainFocus = prop (SProxy :: SProxy "chainFocus")

_chainFocusAppearing :: forall r a. Lens' { chainFocusAppearing :: a | r } a
_chainFocusAppearing = prop (SProxy :: SProxy "chainFocusAppearing")

_chainFocusAge :: forall r a. Lens' { chainFocusAge :: a | r } a
_chainFocusAge = prop (SProxy :: SProxy "chainFocusAge")

_sequenceId :: Lens' AnnotatedTx SequenceId
_sequenceId = _Newtype <<< prop (SProxy :: SProxy "sequenceId")

_dereferencedInputs :: Lens' AnnotatedTx (Array DereferencedInput)
_dereferencedInputs = _Newtype <<< prop (SProxy :: SProxy "dereferencedInputs")

_value :: forall s a r. Newtype s { getValue :: a | r } => Lens' s a
_value = _Newtype <<< prop (SProxy :: SProxy "getValue")

_txIdOf :: Lens' AnnotatedTx TxId
_txIdOf = _Newtype <<< prop (SProxy :: SProxy "txId")

_balances :: Lens' AnnotatedTx (Map BeneficialOwner Value)
_balances = _Newtype <<< prop (SProxy :: SProxy "balances")

_tx :: Lens' AnnotatedTx Tx
_tx = _Newtype <<< prop (SProxy :: SProxy "tx")

_txFee :: Lens' Tx Value
_txFee = _Newtype <<< prop (SProxy :: SProxy "txFee")

_txForge :: Lens' Tx Value
_txForge = _Newtype <<< prop (SProxy :: SProxy "txForge")

_txValidRange :: Lens' Tx (Interval Slot)
_txValidRange = _Newtype <<< prop (SProxy :: SProxy "txValidRange")

_txSignatures :: Lens' Tx (Map PubKey Signature)
_txSignatures = _Newtype <<< prop (SProxy :: SProxy "txSignatures")

_txInputs :: Lens' Tx (Array TxIn)
_txInputs = _Newtype <<< prop (SProxy :: SProxy "txInputs")

_txOutputs :: Lens' Tx (Array TxOut)
_txOutputs = _Newtype <<< prop (SProxy :: SProxy "txOutputs")

_txInRef :: Lens' TxIn TxOutRef
_txInRef = _Newtype <<< prop (SProxy :: SProxy "txInRef")

_txOutRefId :: Lens' TxOutRef TxId
_txOutRefId = _Newtype <<< prop (SProxy :: SProxy "txOutRefId")

_txKeyTxId :: Lens' TxKey TxId
_txKeyTxId = _TxKey <<< prop (SProxy :: SProxy "_txKeyTxId")

_txKeyTxOutRefIdx :: Lens' TxKey BigInteger
_txKeyTxOutRefIdx = _TxKey <<< prop (SProxy :: SProxy "_txKeyTxOutRefIdx")

toBeneficialOwner :: TxOut -> BeneficialOwner
toBeneficialOwner (TxOut { txOutAddress }) = case txOutAddress of
  PubKeyAddress pkh -> OwnedByPubKey pkh
  ScriptAddress vh -> OwnedByScript vh

_findTx :: forall m. Monoid m => TxId -> Fold' m AnnotatedBlockchain AnnotatedTx
_findTx focussedTxId = (_AnnotatedBlocks <<< filtered isAnnotationOf)
  where
  isAnnotationOf :: AnnotatedTx -> Boolean
  isAnnotationOf (AnnotatedTx { txId }) = txId == focussedTxId

-- | Where is this output consumed?
findConsumptionPoint :: BigInteger -> TxId -> AnnotatedBlockchain -> Maybe AnnotatedTx
findConsumptionPoint outputIndex txId = preview (_AnnotatedBlocks <<< filtered isMatchingTx)
  where
  isMatchingTx :: AnnotatedTx -> Boolean
  isMatchingTx tx = preview (_tx <<< _txInputs <<< traversed <<< _txInRef) tx == Just txOutRef

  txOutRef :: TxOutRef
  txOutRef =
    TxOutRef
      { txOutRefId: txId
      , txOutRefIdx: outputIndex
      }

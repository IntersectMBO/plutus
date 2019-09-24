module Chain.Types where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Fold', Iso', Lens', filtered, iso, traversed)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Ledger.Tx (TxOutOf(..), TxOutType(..))
import Ledger.TxId (TxIdOf)
import Playground.Types (AnnotatedTx(..), BeneficialOwner(..), SequenceId)

type TxId
  = TxIdOf String

data ChainFocus
  = FocusTx TxId

_FocusTx :: Iso' ChainFocus TxId
_FocusTx = iso get set
  where
  get (FocusTx txId) = txId

  set = FocusTx

derive instance genericChainFocus :: Generic ChainFocus _

instance showChainFocus :: Show ChainFocus where
  show = genericShow

type State
  = { chainFocus :: Maybe ChainFocus
    , chainFocusAppearing :: Boolean
    , chainFocusAge :: Ordering
    }

_chainFocus :: forall r a. Lens' { chainFocus :: a | r } a
_chainFocus = prop (SProxy :: SProxy "chainFocus")

_chainFocusAppearing :: forall r a. Lens' { chainFocusAppearing :: a | r } a
_chainFocusAppearing = prop (SProxy :: SProxy "chainFocusAppearing")

_chainFocusAge :: forall r a. Lens' { chainFocusAge :: a | r } a
_chainFocusAge = prop (SProxy :: SProxy "chainFocusAge")

_sequenceId :: Lens' AnnotatedTx SequenceId
_sequenceId = _Newtype <<< prop (SProxy :: SProxy "sequenceId")

_txIdOf :: Lens' AnnotatedTx TxId
_txIdOf = _Newtype <<< prop (SProxy :: SProxy "txId")

_txId :: forall a. Lens' (TxIdOf a) a
_txId = _Newtype <<< prop (SProxy :: SProxy "getTxId")

toBeneficialOwner :: TxOutOf String -> BeneficialOwner
toBeneficialOwner (TxOutOf { txOutType, txOutAddress }) = case txOutType of
  PayToPubKey pubKey -> OwnedByPubKey pubKey
  PayToScript _ -> OwnedByScript txOutAddress

_findTx :: forall m. Monoid m => TxId -> Fold' m (Array (Array AnnotatedTx)) AnnotatedTx
_findTx focussedTxId = (traversed <<< traversed <<< filtered isAnnotationOf)
  where
  isAnnotationOf :: AnnotatedTx -> Boolean
  isAnnotationOf (AnnotatedTx { txId }) = txId == focussedTxId

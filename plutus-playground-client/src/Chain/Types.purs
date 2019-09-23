module Chain.Types where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Iso', Lens', iso)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Ledger.Tx (TxOutOf(..), TxOutType(..))
import Playground.Types (AnnotatedTx, BeneficialOwner(..), SequenceId)

data ChainFocus
  = FocusTx AnnotatedTx

_FocusTx :: Iso' ChainFocus AnnotatedTx
_FocusTx = iso get set
  where
    get (FocusTx annotatedTx) = annotatedTx
    set = FocusTx

derive instance genericChainFocus :: Generic ChainFocus _

instance showChainFocus :: Show ChainFocus where
  show = genericShow

type State =
  { chainFocus :: Maybe ChainFocus
  , chainFocusAppearing :: Boolean
  , chainFocusAge :: Ordering
  }

_sequenceId :: Lens' AnnotatedTx SequenceId
_sequenceId = _Newtype <<< prop (SProxy :: SProxy "sequenceId")

toBeneficialOwner :: TxOutOf String -> BeneficialOwner
toBeneficialOwner (TxOutOf {txOutType, txOutAddress}) =
    case txOutType of
        PayToPubKey pubKey -> OwnedByPubKey pubKey
        PayToScript _      -> OwnedByScript txOutAddress

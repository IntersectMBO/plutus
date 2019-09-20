module Chain.Types where

import Prelude

import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Prism', Lens', prism)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Ledger.Tx (AddressOf, TxOutOf(..), TxOutType(..))
import Playground.Types (AnnotatedTx, BeneficialOwner(..), SequenceId)

data ChainFocus
  = FocusTx AnnotatedTx
  | FocusAddress (AddressOf String)

_FocusTx :: Prism' ChainFocus AnnotatedTx
_FocusTx = prism FocusTx case _ of
  FocusTx tx -> Right tx
  other -> Left other

_FocusAddress :: Prism' ChainFocus (AddressOf String)
_FocusAddress = prism FocusAddress case _ of
  FocusAddress address -> Right address
  other -> Left other

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

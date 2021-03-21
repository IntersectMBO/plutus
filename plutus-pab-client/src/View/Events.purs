module View.Events
  ( utxoIndexPane
  ) where

import Prelude
import Bootstrap (badgePrimary_, cardBody_, cardHeader_, card_, nbsp)
import Bootstrap.Extra (preWrap_)
import Chain.View as Chain
import Data.Array as Array
import Data.Foldable.Extra (countConsecutive)
import Data.Lens (view)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Halogen.HTML (HTML, div_, h2_, text)
import Ledger.Index (UtxoIndex)
import Plutus.V1.Ledger.Tx (TxOut, TxOutRef)
import Playground.Lenses (_utxoIndexEntries)
import Plutus.PAB.Events (PABEvent)
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import Types (HAction(..))
import View.Pretty (class Pretty, pretty)

utxoIndexPane :: forall p. UtxoIndex -> HTML p HAction
utxoIndexPane utxoIndex =
  card_
    [ cardHeader_
        [ h2_ [ text "UtxoIndex" ] ]
    , cardBody_
        (utxoEntryPane <$> Map.toUnfoldable (view _utxoIndexEntries utxoIndex))
    ]

utxoEntryPane :: forall p. (TxOutRef /\ TxOut) -> HTML p HAction
utxoEntryPane (txOutRef /\ txOut) = ChainAction <$> Chain.txOutOfView (const Nothing) false txOut Nothing

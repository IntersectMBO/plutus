module View.Events
  ( eventsPane
  , utxoIndexPane
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
import Ledger.Tx (TxOut, TxOutRef)
import Playground.Lenses (_utxoIndexEntries)
import Plutus.SCB.Events (ChainEvent)
import Plutus.SCB.Types (ContractExe)
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
utxoEntryPane (txOutRef /\ txOut) = ChainAction <$> Chain.txOutOfView false mempty txOut Nothing

eventsPane :: forall p i. Array (ChainEvent ContractExe) -> HTML p i
eventsPane events =
  card_
    [ cardHeader_
        [ h2_ [ text "Event log" ]
        , text (show (Array.length events))
        , nbsp
        , text "Event(s)"
        ]
    , cardBody_ [ div_ (countedEventPane <$> countConsecutive events) ]
    ]

countedEventPane :: forall t p i. Pretty t => Int /\ ChainEvent t -> HTML p i
countedEventPane (count /\ event) =
  div_
    [ preWrap_
        [ badgePrimary_
            [ text $ show count <> "x" ]
        , nbsp
        , pretty event
        ]
    ]

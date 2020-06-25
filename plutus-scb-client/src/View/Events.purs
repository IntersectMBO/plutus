module View.Events (eventsPane, transactionPane, utxoIndexPane) where

import Data.Tuple.Nested (type (/\), (/\))
import Halogen.HTML (HTML, b_, code_, div_, h2_, span, span_, text)
import Plutus.SCB.Events (ChainEvent(..))
import Prelude
import Bootstrap (badge, badgePrimary, cardBody_, cardHeader_, card_, nbsp)
import Bootstrap.Extra (preWrap_)
import Data.Array as Array
import Data.Foldable.Extra (countConsecutive)
import Data.Json.JsonMap (JsonMap(..))
import Data.Lens (to, traversed)
import Data.Lens.Extra (toArrayOf)
import Data.String.Extra (abbreviate)
import Halogen.HTML.Properties (classes)
import Ledger.Index (UtxoIndex)
import Ledger.Tx (Tx)
import Ledger.TxId (TxId)
import Plutus.SCB.Events.Contract (ContractEvent, ContractInstanceState(..))
import Plutus.SCB.Events.Node (NodeEvent)
import Plutus.SCB.Events.User (UserEvent(..))
import Plutus.SCB.Events.Wallet (WalletEvent)
import Plutus.SCB.Types (ContractExe(..))

transactionPane ::
  forall p i.
  JsonMap TxId Tx -> HTML p i
transactionPane (JsonMap txMap) =
  card_
    [ cardHeader_
        [ h2_ [ text "Txs" ]
        ]
    , cardBody_
        ( toArrayOf
            ( traversed
                <<< to (\x -> div_ [ code_ [ text $ show x ] ])
            )
            txMap
        )
    ]

utxoIndexPane :: forall p i. UtxoIndex -> HTML p i
utxoIndexPane utxoIndex =
  card_
    [ cardHeader_
        [ h2_ [ text "UtxoIndex" ]
        ]
    , cardBody_ [ div_ [ code_ [ text $ show utxoIndex ] ] ]
    ]

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

countedEventPane :: forall p i. Int /\ ChainEvent ContractExe -> HTML p i
countedEventPane (count /\ event) =
  div_
    [ preWrap_
        [ span [ classes [ badge, badgePrimary ] ]
            [ text $ show count <> "x" ]
        , nbsp
        , showEvent event
        ]
    ]

showEvent :: forall p i. ChainEvent ContractExe -> HTML p i
showEvent (ContractEvent subevent) =
  span_
    [ b_
        [ text "Contract:"
        , nbsp
        ]
    , showContractEvent subevent
    ]

showEvent (UserEvent subevent) =
  span_
    [ b_
        [ text "User:"
        , nbsp
        ]
    , showUserEvent subevent
    ]

showEvent (WalletEvent subevent) =
  span_
    [ b_
        [ text "Wallet:"
        , nbsp
        ]
    , showWalletEvent subevent
    ]

showEvent (NodeEvent subevent) =
  span_
    [ b_
        [ text "Node:"
        , nbsp
        ]
    , showNodeEvent subevent
    ]

showUserEvent :: forall p i. UserEvent ContractExe -> HTML p i
showUserEvent (InstallContract (ContractExe { contractPath })) = text $ "Install " <> contractPath

showUserEvent ( ContractStateTransition
    ( ContractInstanceState
      { csContract
    , csCurrentState
    }
  )
) = text $ "Update " <> show csContract

showNodeEvent :: forall p i. NodeEvent -> HTML p i
showNodeEvent event = text $ abbreviate 200 $ show event

showContractEvent :: forall p i a. Show a => ContractEvent a -> HTML p i
showContractEvent event = text $ abbreviate 200 $ show event

showWalletEvent :: forall p i. WalletEvent -> HTML p i
showWalletEvent event = text $ abbreviate 200 $ show event

module View.Events (eventsPane, utxoIndexPane) where

import Prelude
import Bootstrap (alertDanger_, badgePrimary_, cardBody_, cardHeader_, card_, nbsp)
import Bootstrap.Extra (preWrap_)
import Chain.View as Chain
import Data.Array (length)
import Data.Array as Array
import Data.Foldable.Extra (countConsecutive)
import Data.Lens (view)
import Data.Lens.Extra (toArrayOf)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Tuple.Nested (type (/\), (/\))
import Halogen.HTML (HTML, b_, div_, h2_, span_, text)
import Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription)
import Language.Plutus.Contract.Effects.WriteTx (WriteTxResponse(..))
import Language.Plutus.Contract.Resumable (Response(..))
import Ledger.Index (UtxoIndex)
import Ledger.Tx (Tx(..), TxOut, TxOutRef)
import Playground.Lenses (_endpointValue, _getEndpointDescription, _txConfirmed, _txId, _utxoIndexEntries)
import Plutus.SCB.Events (ChainEvent(..))
import Plutus.SCB.Events.Contract (ContractEvent(..), ContractInstanceState(..), ContractResponse(..))
import Plutus.SCB.Events.Node (NodeEvent(..))
import Plutus.SCB.Events.User (UserEvent(..))
import Plutus.SCB.Events.Wallet (WalletEvent(..))
import Plutus.SCB.Types (ContractExe(..))
import Types (HAction(..), _contractActiveEndpoints, _contractInstanceIdString)

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

countedEventPane :: forall p i. Int /\ ChainEvent ContractExe -> HTML p i
countedEventPane (count /\ event) =
  div_
    [ preWrap_
        [ badgePrimary_
            [ text $ show count <> "x" ]
        , nbsp
        , render event
        ]
    ]

class Render a where
  render :: forall p i. a -> HTML p i

instance renderChainEvent :: Render t => Render (ChainEvent t) where
  render (ContractEvent subevent) = eventWithPrefix "Contract" $ render subevent
  render (UserEvent subevent) = eventWithPrefix "User" $ render subevent
  render (WalletEvent subevent) = eventWithPrefix "Wallet" $ render subevent
  render (NodeEvent subevent) = eventWithPrefix "Node" $ render subevent

eventWithPrefix :: forall i p. String -> HTML p i -> HTML p i
eventWithPrefix prefix content =
  span_
    [ b_
        [ text prefix
        , text ":"
        , nbsp
        ]
    , content
    ]

instance renderUserEvent :: Render t => Render (UserEvent t) where
  render (InstallContract contract) = span_ [ text $ "Install", nbsp, render contract ]
  render (ContractStateTransition instanceState) = render instanceState

instance renderContractExe :: Render ContractExe where
  render ((ContractExe { contractPath })) = text contractPath

instance renderContractInstanceState :: Render t => Render (ContractInstanceState t) where
  render ( ContractInstanceState
      { csContract
    , csCurrentIteration
    , csCurrentState
    , csContractDefinition
    }
  ) =
    span_
      [ text "Update instance "
      , text $ view _contractInstanceIdString csContract
      , text " of contract "
      , render csContractDefinition
      , text " to iteration "
      , text $ show $ unwrap csCurrentIteration
      , div_
          [ nbsp
          , text "with new active endpoint(s): "
          , text $ show $ toArrayOf (_contractActiveEndpoints <<< _getEndpointDescription) csCurrentState
          ]
      ]

instance renderNodeEvent :: Render NodeEvent where
  render event@(SubmittedTx tx) =
    span_
      [ text "SubmittedTx"
      , nbsp
      , render tx
      ]

instance renderContractEvent :: Render t => Render (ContractEvent t) where
  render event@(ContractInboxMessage instanceId response) =
    span_
      [ text "Inbox message for instance "
      , text $ view _contractInstanceIdString instanceId
      , render response
      ]
  render event@(ContractInstanceStateUpdateEvent instanceState) = render instanceState

instance renderResponse :: Render a => Render (Response a) where
  render (Response { rspRqID, rspItID, rspResponse }) =
    span_
      [ text "Request:"
      , nbsp
      , text $ show $ unwrap rspRqID
      , nbsp
      , text "Iteration:"
      , nbsp
      , text $ show $ unwrap rspItID
      , div_ [ render rspResponse ]
      ]

instance renderContractResponse :: Render ContractResponse where
  render (AwaitSlotResponse slot) =
    span_
      [ text "AwaitSlotResponse"
      , nbsp
      , text $ show slot
      ]
  render (AwaitTxConfirmedResponse txConfirmed) =
    span_
      [ text "AwaitTxConfirmedResponse Confirmed:"
      , nbsp
      , text $ view (_txConfirmed <<< _txId) txConfirmed
      ]
  render (UserEndpointResponse endpointDescription endpointValue) =
    span_
      [ text "UserEndpointResponse"
      , nbsp
      , render endpointDescription
      , nbsp
      , text $ view (_endpointValue <<< _Newtype) endpointValue
      ]
  render (OwnPubkeyResponse pubKey) =
    span_
      [ text "OwnPubkeyResponse"
      , nbsp
      , text $ show pubKey
      ]
  render (UtxoAtResponse utxoAtAddress) =
    span_
      [ text "UtxoAtResponse"
      , nbsp
      , text $ show utxoAtAddress
      ]
  render (NextTxAtResponse addressChangeResponse) =
    span_
      [ text "NextTxAtResponse"
      , nbsp
      , text $ show addressChangeResponse
      ]
  render (WriteTxResponse writeTxResponse) =
    span_
      [ text "WriteTxResponse"
      , nbsp
      , render writeTxResponse
      ]

instance renderWriteTxResponse :: Render WriteTxResponse where
  render (WriteTxSuccess tx) = span_ [ text "WriteTxSuccess", nbsp, render tx ]
  render (WriteTxFailed error) =
    alertDanger_
      [ text "WriteTxFailed"
      , nbsp
      , text $ show error
      ]

instance renderTx :: Render Tx where
  render (Tx { txInputs, txOutputs, txSignatures }) =
    span_
      [ text "Tx: "
      , text $ show (length txInputs) <> " inputs, "
      , text $ show (length txOutputs) <> " outputs, "
      , text $ show (Map.size (unwrap txSignatures)) <> " signatures."
      ]

instance renderWalletEvent :: Render WalletEvent where
  render (BalancedTx tx) =
    span_
      [ text "BalancedTx"
      , nbsp
      , render tx
      ]

instance renderEndpointDescription :: Render EndpointDescription where
  render description = text $ show $ view _getEndpointDescription description

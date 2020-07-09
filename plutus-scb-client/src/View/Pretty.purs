module View.Pretty where

import Data.Lens (toArrayOf, view)
import Halogen.HTML (HTML, b_, div_, span_, text)
import Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription)
import Playground.Lenses (_endpointValue, _getEndpointDescription, _txConfirmed, _txId)
import Plutus.SCB.Events (ChainEvent(..))
import Plutus.SCB.Events.Contract (ContractEvent(..), ContractInstanceState(..), ContractResponse(..))
import Plutus.SCB.Events.User (UserEvent(..))
import Plutus.SCB.Types (ContractExe(..))
import Types (_contractActiveEndpoints, _contractInstanceIdString)
import Bootstrap (alertDanger_, nbsp)
import Data.Array (length)
import Prelude
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Map
import Data.Newtype (unwrap)
import Language.Plutus.Contract.Effects.WriteTx (WriteTxResponse(..))
import Language.Plutus.Contract.Resumable (Response(..))
import Ledger.Tx (Tx(..))
import Plutus.SCB.Events.Node (NodeEvent(..))
import Plutus.SCB.Events.Wallet (WalletEvent(..))

class Pretty a where
  pretty :: forall p i. a -> HTML p i

instance prettyChainEvent :: Pretty t => Pretty (ChainEvent t) where
  pretty (ContractEvent subevent) = eventWithPrefix "Contract" $ pretty subevent
  pretty (UserEvent subevent) = eventWithPrefix "User" $ pretty subevent
  pretty (WalletEvent subevent) = eventWithPrefix "Wallet" $ pretty subevent
  pretty (NodeEvent subevent) = eventWithPrefix "Node" $ pretty subevent

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

instance prettyUserEvent :: Pretty t => Pretty (UserEvent t) where
  pretty (InstallContract contract) = span_ [ text $ "Install", nbsp, pretty contract ]
  pretty (ContractStateTransition instanceState) = pretty instanceState

instance prettyContractExe :: Pretty ContractExe where
  pretty ((ContractExe { contractPath })) = text contractPath

instance prettyContractInstanceState :: Pretty t => Pretty (ContractInstanceState t) where
  pretty ( ContractInstanceState
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
      , pretty csContractDefinition
      , text " to iteration "
      , text $ show $ unwrap csCurrentIteration
      , div_
          [ nbsp
          , text "with new active endpoint(s): "
          , text $ show $ toArrayOf (_contractActiveEndpoints <<< _getEndpointDescription) csCurrentState
          ]
      ]

instance prettyNodeEvent :: Pretty NodeEvent where
  pretty event@(SubmittedTx tx) =
    span_
      [ text "SubmittedTx"
      , nbsp
      , pretty tx
      ]

instance prettyContractEvent :: Pretty t => Pretty (ContractEvent t) where
  pretty event@(ContractInboxMessage instanceId response) =
    span_
      [ text "Inbox message for instance "
      , text $ view _contractInstanceIdString instanceId
      , pretty response
      ]
  pretty event@(ContractInstanceStateUpdateEvent instanceState) = pretty instanceState

instance prettyResponse :: Pretty a => Pretty (Response a) where
  pretty (Response { rspRqID, rspItID, rspResponse }) =
    span_
      [ text "Request:"
      , nbsp
      , text $ show $ unwrap rspRqID
      , nbsp
      , text "Iteration:"
      , nbsp
      , text $ show $ unwrap rspItID
      , div_ [ pretty rspResponse ]
      ]

instance prettyContractResponse :: Pretty ContractResponse where
  pretty (AwaitSlotResponse slot) =
    span_
      [ text "AwaitSlotResponse"
      , nbsp
      , text $ show slot
      ]
  pretty (AwaitTxConfirmedResponse txConfirmed) =
    span_
      [ text "AwaitTxConfirmedResponse Confirmed:"
      , nbsp
      , text $ view (_txConfirmed <<< _txId) txConfirmed
      ]
  pretty (UserEndpointResponse endpointDescription endpointValue) =
    span_
      [ text "UserEndpointResponse"
      , nbsp
      , pretty endpointDescription
      , nbsp
      , text $ view (_endpointValue <<< _Newtype) endpointValue
      ]
  pretty (OwnPubkeyResponse pubKey) =
    span_
      [ text "OwnPubkeyResponse"
      , nbsp
      , text $ show pubKey
      ]
  pretty (UtxoAtResponse utxoAtAddress) =
    span_
      [ text "UtxoAtResponse"
      , nbsp
      , text $ show utxoAtAddress
      ]
  pretty (NextTxAtResponse addressChangeResponse) =
    span_
      [ text "NextTxAtResponse"
      , nbsp
      , text $ show addressChangeResponse
      ]
  pretty (WriteTxResponse writeTxResponse) =
    span_
      [ text "WriteTxResponse"
      , nbsp
      , pretty writeTxResponse
      ]

instance prettyWriteTxResponse :: Pretty WriteTxResponse where
  pretty (WriteTxSuccess tx) = span_ [ text "WriteTxSuccess", nbsp, pretty tx ]
  pretty (WriteTxFailed error) =
    alertDanger_
      [ text "WriteTxFailed"
      , nbsp
      , text $ show error
      ]

instance prettyTx :: Pretty Tx where
  pretty (Tx { txInputs, txOutputs, txSignatures }) =
    span_
      [ text "Tx: "
      , text $ show (length txInputs) <> " inputs, "
      , text $ show (length txOutputs) <> " outputs, "
      , text $ show (Map.size (unwrap txSignatures)) <> " signatures."
      ]

instance prettyWalletEvent :: Pretty WalletEvent where
  pretty (BalancedTx tx) =
    span_
      [ text "BalancedTx"
      , nbsp
      , pretty tx
      ]

instance prettyEndpointDescription :: Pretty EndpointDescription where
  pretty description = text $ show $ view _getEndpointDescription description

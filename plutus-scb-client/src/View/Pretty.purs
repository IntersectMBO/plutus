module View.Pretty where

import Prelude
import Bootstrap (alertDanger_, nbsp)
import Data.Array (length)
import Data.Lens (toArrayOf, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Map
import Data.Newtype (unwrap)
import Halogen.HTML (HTML, b_, div_, span_, text)
import Language.Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint, EndpointDescription)
import Language.Plutus.Contract.Effects.WriteTx (WriteTxResponse(..))
import Language.Plutus.Contract.Resumable (Response(..))
import Ledger.Constraints.OffChain (UnbalancedTx(..))
import Ledger.Tx (Tx(..))
import Playground.Lenses (_aeDescription, _endpointValue, _getEndpointDescription, _txConfirmed, _txId)
import Plutus.SCB.Events (ChainEvent(..))
import Plutus.SCB.Events.Contract (ContractEvent(..), ContractInstanceState(..), ContractResponse(..), ContractSCBRequest(..))
import Plutus.SCB.Events.Node (NodeEvent(..))
import Plutus.SCB.Events.User (UserEvent(..))
import Plutus.SCB.Events.Wallet (WalletEvent(..))
import Plutus.SCB.Types (ContractExe(..))
import Types (_contractActiveEndpoints, _contractInstanceIdString)

class Pretty a where
  pretty :: forall p i. a -> HTML p i

instance prettyChainEvent :: Pretty t => Pretty (ChainEvent t) where
  pretty (ContractEvent subevent) = withHeading "Contract" subevent
  pretty (UserEvent subevent) = withHeading "User" subevent
  pretty (WalletEvent subevent) = withHeading "Wallet" subevent
  pretty (NodeEvent subevent) = withHeading "Node" subevent

withHeading :: forall i p a. Pretty a => String -> a -> HTML p i
withHeading prefix content =
  span_
    [ b_
        [ text prefix
        , text ":"
        , nbsp
        ]
    , pretty content
    ]

instance prettyUserEvent :: Pretty t => Pretty (UserEvent t) where
  pretty (InstallContract contract) = span_ [ text $ "Install:", nbsp, pretty contract ]

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
      [ text "SubmittedTx:"
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
      [ text "AwaitSlotResponse:"
      , nbsp
      , text $ show slot
      ]
  pretty (AwaitTxConfirmedResponse txConfirmed) =
    span_
      [ text "AwaitTxConfirmedResponse:"
      , nbsp
      , text $ view (_txConfirmed <<< _txId) txConfirmed
      ]
  pretty (UserEndpointResponse endpointDescription endpointValue) =
    span_
      [ text "UserEndpointResponse:"
      , nbsp
      , pretty endpointDescription
      , nbsp
      , text $ view (_endpointValue <<< _Newtype) endpointValue
      ]
  pretty (OwnPubkeyResponse pubKey) =
    span_
      [ text "OwnPubkeyResponse:"
      , nbsp
      , text $ show pubKey
      ]
  pretty (UtxoAtResponse utxoAtAddress) =
    span_
      [ text "UtxoAtResponse:"
      , nbsp
      , text $ show utxoAtAddress
      ]
  pretty (NextTxAtResponse addressChangeResponse) =
    span_
      [ text "NextTxAtResponse:"
      , nbsp
      , text $ show addressChangeResponse
      ]
  pretty (WriteTxResponse writeTxResponse) =
    span_
      [ text "WriteTxResponse:"
      , nbsp
      , pretty writeTxResponse
      ]

instance prettyContractSCBRequest :: Pretty ContractSCBRequest where
  pretty (AwaitSlotRequest slot) =
    span_
      [ text "AwaitSlotRequest:"
      , nbsp
      , text $ show slot
      ]
  pretty (AwaitTxConfirmedRequest txId) =
    span_
      [ text "AwaitTxConfirmedRequest:"
      , nbsp
      , text $ view _txId txId
      ]
  pretty (UserEndpointRequest activeEndpoint) =
    span_
      [ text "UserEndpointRequest:"
      , nbsp
      , pretty activeEndpoint
      ]
  pretty (OwnPubkeyRequest pubKey) =
    span_
      [ text "OwnPubkeyRequest:"
      , nbsp
      , text $ show pubKey
      ]
  pretty (UtxoAtRequest utxoAtAddress) =
    span_
      [ text "UtxoAtRequest:"
      , nbsp
      , text $ show utxoAtAddress
      ]
  pretty (NextTxAtRequest addressChangeRequest) =
    span_
      [ text "NextTxAtRequest:"
      , nbsp
      , text $ show addressChangeRequest
      ]
  pretty (WriteTxRequest writeTxRequest) =
    span_
      [ text "WriteTxRequest:"
      , nbsp
      , pretty writeTxRequest
      ]

instance prettyWriteTxResponse :: Pretty WriteTxResponse where
  pretty (WriteTxSuccess tx) = span_ [ text "WriteTxSuccess:", nbsp, pretty tx ]
  pretty (WriteTxFailed error) =
    alertDanger_
      [ text "WriteTxFailed:"
      , nbsp
      , text $ show error
      ]

instance prettyUnbalancedTx :: Pretty UnbalancedTx where
  pretty (UnbalancedTx { unBalancedTxTx: (Tx { txInputs, txOutputs, txSignatures }) }) =
    span_
      [ text "UnbalancedTx:"
      , nbsp
      , withBasicPlural (length txInputs) "input"
      , text ", "
      , withBasicPlural (length txOutputs) "output"
      , text ", "
      , withBasicPlural (Map.size (unwrap txSignatures)) "signature"
      , text "."
      ]

instance prettyTx :: Pretty Tx where
  pretty (Tx { txInputs, txOutputs, txSignatures }) =
    span_
      [ text "Tx:"
      , nbsp
      , withBasicPlural (length txInputs) "input"
      , text ", "
      , withBasicPlural (length txOutputs) "output"
      , text ", "
      , withBasicPlural (Map.size (unwrap txSignatures)) "signature"
      , text "."
      ]

instance prettyWalletEvent :: Pretty WalletEvent where
  pretty (BalancedTx tx) =
    span_
      [ text "BalancedTx:"
      , nbsp
      , pretty tx
      ]

instance prettyActiveEndpoint :: Pretty ActiveEndpoint where
  pretty endpoint = pretty $ view _aeDescription endpoint

instance prettyEndpointDescription :: Pretty EndpointDescription where
  pretty description = text $ show $ view _getEndpointDescription description

-- | Yes, this is dumb and only handles _most_ English words, but it's and better than saying '1 input(s)'.
-- And hey, "most English words" is still a lot of words.
withBasicPlural :: forall p i. Int -> String -> HTML p i
withBasicPlural n name =
  span_
    [ text $ show n
    , nbsp
    , text $ name <> (if n == 1 then "" else "s")
    ]

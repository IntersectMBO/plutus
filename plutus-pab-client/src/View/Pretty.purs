module View.Pretty where

import Prelude
import Bootstrap (alertDanger_, nbsp)
import Data.Array (length)
import Data.Lens (view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Map
import Data.Newtype (unwrap)
import Halogen.HTML (HTML, b_, div_, span_, text)
import Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint)
import Plutus.Contract.Effects.WriteTx (WriteTxResponse(..))
import Plutus.Contract.Resumable (Response(..))
import Ledger.Constraints.OffChain (UnbalancedTx(..))
import Plutus.V1.Ledger.Tx (Tx(..))
import Playground.Lenses (_aeDescription, _endpointValue, _getEndpointDescription, _txConfirmed, _txId)
import Plutus.PAB.Events.Contract (ContractResponse(..), ContractPABRequest(..))
import Plutus.PAB.Events (PABEvent(..))
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe(..))
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse(..))
import Plutus.PAB.Webserver.Types (ContractActivationArgs(..))
import Wallet.Types (EndpointDescription)
import Types (_contractInstanceIdString)

class Pretty a where
  pretty :: forall p i. a -> HTML p i

instance prettyPABEvent :: Pretty t => Pretty (PABEvent t) where
  pretty e =
    withHeading "PAB"
      $ case e of
          InstallContract contract -> span_ [ text $ "Install contract:", nbsp, pretty contract ]
          UpdateContractInstanceState (ContractActivationArgs { caID }) instanceId (PartiallyDecodedResponse { hooks }) ->
            span_
              [ text "Update instance "
              , text (view _contractInstanceIdString instanceId)
              , text " of contract "
              , pretty caID
              , div_
                  [ nbsp
                  , text "with new active endpoint(s): "
                  , text $ show hooks
                  ]
              ]
          SubmitTx tx -> span_ [ text "SubmittedTx:", nbsp, pretty tx ]

withHeading :: forall i p. String -> HTML p i -> HTML p i
withHeading prefix content =
  span_
    [ b_
        [ text prefix
        , text ":"
        , nbsp
        ]
    , content
    ]

instance prettyContractExe :: Pretty ContractExe where
  pretty ((ContractExe { contractPath })) = text contractPath

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
  pretty (AddressChangedAtResponse addressChangeResponse) =
    span_
      [ text "AddressChangedAtResponse:"
      , nbsp
      , text $ show addressChangeResponse
      ]
  pretty (WriteTxResponse writeTxResponse) =
    span_
      [ text "WriteTxResponse:"
      , nbsp
      , pretty writeTxResponse
      ]
  pretty (OwnInstanceResponse ownInstanceResponse) =
    span_
      [ text "OwnInstanceResponse:"
      , nbsp
      , text $ view _contractInstanceIdString ownInstanceResponse
      ]
  pretty (NotificationResponse notificationResponse) =
    span_
      [ text "NotificationResponse:"
      , nbsp
      , text $ show notificationResponse
      ]

instance prettyContractPABRequest :: Pretty ContractPABRequest where
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
  pretty (AddressChangedAtRequest addressChangeRequest) =
    span_
      [ text "AddressChangedAtRequest:"
      , nbsp
      , text $ show addressChangeRequest
      ]
  pretty (WriteTxRequest writeTxRequest) =
    span_
      [ text "WriteTxRequest:"
      , nbsp
      , pretty writeTxRequest
      ]
  pretty (OwnInstanceIdRequest ownInstanceIdRequest) =
    span_
      [ text "OwnInstanceIdRequest:"
      , nbsp
      , text $ show ownInstanceIdRequest
      ]
  pretty (SendNotificationRequest sendNotificationRequest) =
    span_
      [ text "SendNotificationRequest:"
      , nbsp
      , text $ show sendNotificationRequest
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
      , withBasicPlural (Map.size txSignatures) "signature"
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
      , withBasicPlural (Map.size txSignatures) "signature"
      , text "."
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

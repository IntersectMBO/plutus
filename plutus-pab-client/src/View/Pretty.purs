module View.Pretty where

import Prelude
import Bootstrap (alertDanger_, nbsp)
import ContractExample (ExampleContracts)
import Data.Array (length)
import Data.Either (Either(..))
import Data.Lens (view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Map
import Data.Newtype (unwrap)
import Halogen.HTML (HTML, b_, div_, span_, text)
import Plutus.Contract.Effects (ActiveEndpoint, BalanceTxResponse(..), WriteBalancedTxResponse(..), PABReq(..), PABResp(..))
import Plutus.Contract.Resumable (Response(..))
import Ledger.Constraints.OffChain (UnbalancedTx(..))
import Plutus.V1.Ledger.Interval (Interval(..), Extended(..), LowerBound(..), UpperBound(..))
import Plutus.V1.Ledger.Slot (Slot(..))
import Plutus.V1.Ledger.Time (POSIXTime(..))
import Plutus.V1.Ledger.Tx (Tx(..))
import Playground.Lenses (_aeDescription, _endpointValue, _getEndpointDescription, _txId)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse(..))
import Plutus.PAB.Webserver.Types (ContractActivationArgs(..))
import Wallet.Types (EndpointDescription)
import Types (_contractInstanceIdString)

class Pretty a where
  pretty :: forall p i. a -> HTML p i

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

instance prettyExampleContracts :: Pretty ExampleContracts where
  pretty = text <<< show

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

instance prettyPABResp :: Pretty PABResp where
  pretty (AwaitSlotResp slot) =
    span_
      [ text "AwaitSlotResponse:"
      , nbsp
      , text $ show slot
      ]
  pretty (CurrentSlotResp slot) =
    span_
      [ text "CurrentSlotResp:"
      , nbsp
      , text $ show slot
      ]
  pretty (AwaitTimeResp time) =
    span_
      [ text "AwaitTimeResponse:"
      , nbsp
      , text $ show time
      ]
  pretty (CurrentTimeResp time) =
    span_
      [ text "CurrentTimeResp:"
      , nbsp
      , text $ show time
      ]
  pretty (AwaitTxStatusChangeResp txConfirmed txStatus) =
    span_
      [ text "AwaitTxStatusChangeResponse:"
      , nbsp
      , text $ view _txId txConfirmed
      , nbsp
      , text $ show txStatus
      ]
  pretty (ExposeEndpointResp endpointDescription endpointValue) =
    span_
      [ text "UserEndpointResponse:"
      , nbsp
      , pretty endpointDescription
      , nbsp
      , text $ view (_endpointValue <<< _Newtype) endpointValue
      ]
  pretty (OwnPublicKeyResp pubKey) =
    span_
      [ text "OwnPublicKeyResponse:"
      , nbsp
      , text $ show pubKey
      ]
  pretty (UtxoAtResp utxoAtAddress) =
    span_
      [ text "UtxoAtResponse:"
      , nbsp
      , text $ show utxoAtAddress
      ]
  pretty (ChainIndexQueryResp chainIndexQueryResponse) =
    span_
      [ text "ChainIndexQueryResponse:"
      , nbsp
      , text $ show chainIndexQueryResponse
      ]
  pretty (AddressChangeResp addressChangeResponse) =
    span_
      [ text "AddressChangedAtResponse:"
      , nbsp
      , text $ show addressChangeResponse
      ]
  pretty (BalanceTxResp balanceTxResponse) =
    span_
      [ text "BalanceTxResponse:"
      , nbsp
      , pretty balanceTxResponse
      ]
  pretty (WriteBalancedTxResp writeBalancedTxResponse) =
    span_
      [ text "WriteBalancedTxResponse:"
      , nbsp
      , pretty writeBalancedTxResponse
      ]
  pretty (OwnContractInstanceIdResp ownInstanceResponse) =
    span_
      [ text "OwnInstanceResponse:"
      , nbsp
      , text $ view _contractInstanceIdString ownInstanceResponse
      ]
  pretty (PosixTimeRangeToContainedSlotRangeResp (Left slotConversionError)) =
    span_
      [ text "SlotConversionError:"
      , nbsp
      , text $ show slotConversionError
      ]
  pretty (PosixTimeRangeToContainedSlotRangeResp (Right slotRange)) =
    span_
      [ text "SlotRange:"
      , nbsp
      , pretty slotRange
      ]
  pretty (AwaitUtxoSpentResp _) =
    span_
      [ text "AwaitUtxoSpentResp"
      ]
  pretty (AwaitUtxoProducedResp _) =
    span_
      [ text "AwaitUtxoProducedResp"
      ]

instance prettyContractPABRequest :: Pretty PABReq where
  pretty (AwaitSlotReq slot) =
    span_
      [ text "AwaitSlotRequest:"
      , nbsp
      , text $ show slot
      ]
  pretty CurrentSlotReq =
    span_
      [ text "CurrentSlotRequest"
      ]
  pretty (AwaitTimeReq time) =
    span_
      [ text "AwaitTimeRequest:"
      , nbsp
      , text $ show time
      ]
  pretty CurrentTimeReq =
    span_
      [ text "CurrentTimeRequest"
      ]
  pretty (AwaitTxStatusChangeReq txId) =
    span_
      [ text "AwaitTxStatusChangeReq:"
      , nbsp
      , text $ view _txId txId
      ]
  pretty (ExposeEndpointReq activeEndpoint) =
    span_
      [ text "UserEndpointRequest:"
      , nbsp
      , pretty activeEndpoint
      ]
  pretty OwnPublicKeyReq =
    span_
      [ text "OwnPubkeyRequest"
      ]
  pretty (UtxoAtReq utxoAtAddress) =
    span_
      [ text "UtxoAtRequest:"
      , nbsp
      , text $ show utxoAtAddress
      ]
  pretty (ChainIndexQueryReq chainIndexQueryRequest) =
    span_
      [ text "ChainIndexQueryRequest:"
      , nbsp
      , text $ show chainIndexQueryRequest
      ]
  pretty (AddressChangeReq addressChangeRequest) =
    span_
      [ text "AddressChangedAtRequest:"
      , nbsp
      , text $ show addressChangeRequest
      ]
  pretty (BalanceTxReq balanceTxRequest) =
    span_
      [ text "BalanceTxRequest:"
      , nbsp
      , pretty balanceTxRequest
      ]
  pretty (WriteBalancedTxReq writeBalancedTxRequest) =
    span_
      [ text "WriteBalancedTxRequest:"
      , nbsp
      , pretty writeBalancedTxRequest
      ]
  pretty OwnContractInstanceIdReq =
    span_
      [ text "OwnInstanceIdRequest"
      ]
  pretty (PosixTimeRangeToContainedSlotRangeReq timeRange) =
    span_
      [ text "PosixTimeRangeToContainedSlotRangeReq:"
      , nbsp
      , pretty timeRange
      ]
  pretty (AwaitUtxoSpentReq _) =
    span_
      [ text "AwaitUtxoSpentReq"
      ]
  pretty (AwaitUtxoProducedReq _) =
    span_
      [ text "AwaitUtxoProducedReq"
      ]

instance prettyBalanceTxResponse :: Pretty BalanceTxResponse where
  pretty (BalanceTxSuccess tx) = span_ [ text "BalanceTxSuccess:", nbsp, pretty tx ]
  pretty (BalanceTxFailed error) =
    alertDanger_
      [ text "BalanceTxFailed:"
      , nbsp
      , text $ show error
      ]

instance prettyWriteBalancedTxResponse :: Pretty WriteBalancedTxResponse where
  pretty (WriteBalancedTxSuccess tx) = span_ [ text "WriteBalancedTxSuccess:", nbsp, pretty tx ]
  pretty (WriteBalancedTxFailed error) =
    alertDanger_
      [ text "WriteBalancedTxFailed:"
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

instance prettyLowerBound :: Pretty a => Pretty (LowerBound a) where
  pretty (LowerBound PosInf _) = text "(+∞"
  pretty (LowerBound NegInf _) = text "(-∞"
  pretty (LowerBound (Finite a) true) = span_ [ text "[", pretty a ]
  pretty (LowerBound (Finite a) false) = span_ [ text "(", pretty a ]

instance prettyUpperBound :: Pretty a => Pretty (UpperBound a) where
  pretty (UpperBound PosInf _) = text "+∞)"
  pretty (UpperBound NegInf _) = text "-∞)"
  pretty (UpperBound (Finite a) true) = span_ [ pretty a, text "]" ]
  pretty (UpperBound (Finite a) false) = span_ [ pretty a, text ")" ]

instance prettyInterval :: Pretty a => Pretty (Interval a) where
  pretty (Interval { ivFrom, ivTo }) = span_ [ pretty ivFrom, text ", ", pretty ivTo ]

instance prettyPOSIXTime :: Pretty POSIXTime where
  pretty (POSIXTime { getPOSIXTime }) = span_ [ text "POSIXTime:", nbsp, text $ show getPOSIXTime ]

instance prettySlot :: Pretty Slot where
  pretty (Slot { getSlot }) = span_ [ text "Slot:", nbsp, text $ show getSlot ]

-- | Yes, this is dumb and only handles _most_ English words, but it's and better than saying '1 input(s)'.
-- And hey, "most English words" is still a lot of words.
withBasicPlural :: forall p i. Int -> String -> HTML p i
withBasicPlural n name =
  span_
    [ text $ show n
    , nbsp
    , text $ name <> (if n == 1 then "" else "s")
    ]

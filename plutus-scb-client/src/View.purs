module View (render) where

import Playground.Lenses
import AjaxUtils (ajaxErrorPane)
import Bootstrap (badge, badgePrimary, cardBody_, cardHeader_, card_, col10_, col12_, col2_, col5_, col8_, container_, nbsp, row_)
import Bootstrap.Extra (preWrap_)
import Chain.Types (AnnotatedBlockchain(..), ChainFocus)
import Chain.Types as Chain
import Chain.View (chainView)
import Data.Array as Array
import Data.FunctorWithIndex (mapWithIndex)
import Data.Json.JsonMap (JsonMap(..))
import Data.Json.JsonUUID (_JsonUUID)
import Data.Lens (to, traversed, view)
import Data.Lens.Extra (toArrayOf)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.RawJson as RawJson
import Data.Tuple (Tuple)
import Data.Tuple.Nested (type (/\), (/\))
import Data.UUID as UUID
import Effect.Aff.Class (class MonadAff)
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, b_, code_, div, div_, h2_, h3_, pre_, span, span_, text)
import Halogen.HTML.Properties (class_, classes)
import Icons (Icon(..), icon)
import Ledger.Crypto (PubKeyHash)
import Ledger.Index (UtxoIndex)
import Ledger.Tx (Tx)
import Ledger.TxId (TxId)
import Network.RemoteData (RemoteData(..))
import Playground.Schema (actionArgumentForm)
import Playground.Types (_FunctionSchema)
import Playground.Lenses (_endpointDescription, _getEndpointDescription)
import Plutus.SCB.Events (ChainEvent(..))
import Plutus.SCB.Events.Contract (ContractEvent, ContractInstanceId, ContractInstanceState(..))
import Plutus.SCB.Events.Node (NodeEvent(..))
import Plutus.SCB.Events.User (UserEvent(..))
import Plutus.SCB.Events.Wallet (WalletEvent)
import Plutus.SCB.Types (ContractExe(..))
import Plutus.SCB.Webserver.Types (ContractSignatureResponse(..), FullReport(..))
import Prelude (class Eq, class Show, otherwise, show, ($), (+), (<$>), (<<<), (<>), (==))
import Schema.Types (Signatures, SimulationAction, FormArgument, mkInitialValue, toArgument)
import Types (HAction(..), State(State), WebData, _contractInstanceId, _csContract, _csCurrentState, _hooks)
import Validation (_arguments)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Rollup.Types (AnnotatedTx)

render ::
  forall m slots.
  MonadAff m =>
  State -> ComponentHTML HAction slots m
render (State { chainState, fullReport, contractSignatures }) =
  div
    [ class_ $ ClassName "main-frame" ]
    [ container_
        [ div_
            $ case fullReport of
                Success report -> [ fullReportPane chainState contractSignatures report ]
                Failure error -> [ ajaxErrorPane error ]
                Loading -> [ icon Spinner ]
                NotAsked -> [ icon Spinner ]
        ]
    ]

fullReportPane ::
  forall p.
  Chain.State ->
  Map ContractInstanceId (WebData (ContractSignatureResponse ContractExe)) ->
  FullReport ContractExe ->
  HTML p HAction
fullReportPane chainState contractSignatures fullReport@(FullReport { events, latestContractStatuses, transactionMap, utxoIndex, annotatedBlockchain, walletMap }) =
  row_
    [ col10_ [ contractStatusesPane contractSignatures latestContractStatuses ]
    , col12_ [ ChainAction <<< Just <$> annotatedBlockchainPane chainState walletMap annotatedBlockchain ]
    , col12_ [ eventsPane events ]
    , col8_ [ transactionPane transactionMap ]
    , col8_ [ utxoIndexPane utxoIndex ]
    ]

contractStatusesPane ::
  forall p t.
  Map ContractInstanceId (WebData (ContractSignatureResponse t)) ->
  Array (ContractInstanceState t) ->
  HTML p HAction
contractStatusesPane contractSignatures latestContractStatuses =
  card_
    [ cardHeader_
        [ h2_ [ text "Active Contracts" ]
        ]
    , cardBody_
        [ InvokeContractEndpoint <$> div_ (contractStatusPane contractSignatures <$> latestContractStatuses) ]
    ]

contractStatusPane ::
  forall p t.
  Map ContractInstanceId (WebData (ContractSignatureResponse t)) ->
  ContractInstanceState t -> HTML p SimulationAction
contractStatusPane contractSignatures contractInstance =
  row_
    [ col2_ [ h3_ [ text $ view (_csContract <<< _contractInstanceId <<< _JsonUUID <<< to UUID.toString) contractInstance ] ]
    , col5_ [ pre_ [ text $ RawJson.pretty $ view (_csCurrentState <<< _hooks) contractInstance ] ]
    , col5_
        $ case Map.lookup (view _csContract contractInstance) contractSignatures of
            Just (Success (ContractSignatureResponse signature)) -> [ foo signature ]
            Just (Failure err) -> [ ajaxErrorPane err ]
            Just Loading -> [ icon Spinner ]
            Just NotAsked -> []
            Nothing -> []
    ]

foo :: forall p. Signatures -> HTML p SimulationAction
foo signatures =
  let
    initialValue = mkInitialValue [] 0
  in
    div_
      ( mapWithIndex
          ( \index sig ->
              let
                formArguments :: Array FormArgument
                formArguments = toArgument initialValue <$> view (_FunctionSchema <<< _arguments) sig
              in
                card_
                  [ cardHeader_ [ h2_ [ text $ view (_FunctionSchema <<< _endpointDescription <<< _getEndpointDescription) sig ] ]
                  , cardBody_ [ actionArgumentForm index formArguments ]
                  ]
          )
          signatures
      )

annotatedBlockchainPane :: forall p. Chain.State -> JsonMap PubKeyHash Wallet -> Array (Array AnnotatedTx) -> HTML p ChainFocus
annotatedBlockchainPane chainState (JsonMap walletMap) chain =
  card_
    [ cardHeader_
        [ h2_ [ text "Blockchain" ]
        ]
    , cardBody_
        [ chainView chainState walletMap $ AnnotatedBlockchain chain
        ]
    ]

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
showNodeEvent (BlockAdded []) = text $ "Empty block(s) added"

showNodeEvent event = text $ show event

showContractEvent :: forall p i a. Show a => ContractEvent a -> HTML p i
showContractEvent event = text $ show event

showWalletEvent :: forall p i. WalletEvent -> HTML p i
showWalletEvent event = text $ show event

countConsecutive :: forall a. Eq a => Array a -> Array (Tuple Int a)
countConsecutive = h <<< f
  where
  f :: Array a -> (Int /\ Maybe a /\ Array (Tuple Int a))
  f = Array.foldl g (0 /\ Nothing /\ [])

  g :: (Int /\ Maybe a /\ Array (Tuple Int a)) -> a -> (Int /\ Maybe a /\ Array (Tuple Int a))
  g (count /\ Nothing /\ accum) y = (1 /\ Just y /\ accum)

  g (count /\ Just x /\ accum) y
    | x == y = ((count + 1) /\ Just x /\ accum)
    | otherwise = (1 /\ Just y /\ Array.snoc accum (count /\ x))

  h (count /\ Nothing /\ accum) = accum

  h (count /\ Just x /\ accum) = Array.snoc accum (count /\ x)
